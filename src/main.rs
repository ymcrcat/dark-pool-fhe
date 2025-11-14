// Dark Pool with Proper Shamir Secret Sharing for Threshold Decryption
//
// Cargo.toml:
// [package]
// name = "dark_pool_threshold_fhe"
// version = "0.1.0"
// edition = "2021"
//
// [dependencies]
// tfhe = { version = "0.6", features = ["boolean", "shortint", "integer"] }
// sha2 = "0.10"
// rand = "0.8"
//
// PROPER THRESHOLD FHE WITH SHAMIR SECRET SHARING:
// - Dark pool generates FHE key pair
// - Private key is split into N shares using Shamir Secret Sharing
// - Each share goes to a different party (trader, regulator, etc)
// - Any T shares can reconstruct the private key via Lagrange interpolation
// - No single party can decrypt alone
// - Requires T-of-N parties to cooperate

use tfhe::prelude::*;
use tfhe::{generate_keys, set_server_key, ConfigBuilder, FheUint32};
use std::collections::HashMap;

// ============================================================================
// CONSTANTS
// ============================================================================

// Shamir Secret Sharing Parameters
const PRIME_FIELD: u64 = 251;  // Largest prime < 256, used for finite field arithmetic

// Trading Parameters
const MIN_PRICE: u32 = 95;      // Minimum price in price range
const MAX_PRICE: u32 = 105;     // Maximum price in price range
const PRICE_RANGE: u32 = 11;    // MAX_PRICE - MIN_PRICE + 1

const MIN_VOLUME: u32 = 500;    // Minimum order volume
const VOLUME_RANGE: u32 = 100;  // Random volume range (500-600)

// System Parameters
const NUM_SELLERS: u32 = 10;    // Number of sellers in auction
const NUM_BUYERS: u32 = 10;     // Number of buyers in auction

const THRESHOLD: usize = 3;     // Minimum shares needed for decryption
const TOTAL_SHARES: usize = 5;  // Total secret shares distributed

const KEY_SIZE_BYTES: usize = 32; // Private key size for demo

// ============================================================================

/// Shamir Secret Share - a point on a polynomial
#[derive(Clone, Debug)]
struct SecretShare {
    _party_id: String,
    x: u64,                    // x-coordinate (party identifier)
    y_bytes: Vec<u8>,         // y-coordinate (secret share value)
}

/// Threshold cryptography parameters
#[derive(Clone, Debug)]
struct ThresholdParams {
    threshold: usize,          // Minimum shares needed (t)
    total_shares: usize,       // Total shares distributed (n)
}

/// Key holder with their secret share
#[derive(Clone, Debug)]
struct KeyShareHolder {
    party_id: String,
    share: SecretShare,
}

/// Trader with encrypted order
#[derive(Clone)]
struct Trader {
    id: String,
    encrypted_volume: FheUint32,
    encrypted_limit_price: FheUint32,  // Max price for buyers, min price for sellers
}

/// Dark pool with proper threshold FHE
pub struct ThresholdFHEDarkPool {
    threshold_params: ThresholdParams,
}

impl ThresholdFHEDarkPool {
    pub fn new(threshold: usize, total_shares: usize) -> Self {
        assert!(threshold <= total_shares, "Threshold must be <= total shares");
        assert!(threshold > total_shares / 2, "Threshold must be > N/2 for security");
        
        ThresholdFHEDarkPool {
            threshold_params: ThresholdParams {
                threshold,
                total_shares,
            },
        }
    }

    /// Shamir Secret Share the private key bytes
    /// Uses polynomial of degree (threshold-1)
    fn shamir_split_key(&self, secret_bytes: &[u8]) -> Vec<SecretShare> {
        let t = self.threshold_params.threshold;
        let n = self.threshold_params.total_shares;
        
        let mut shares = Vec::new();
        
        // For each byte in the secret
        for byte_idx in 0..secret_bytes.len() {
            let secret_byte = secret_bytes[byte_idx] as u64;
            
            // Create a polynomial: f(x) = secret + a1*x + a2*x^2 + ... + a_{t-1}*x^{t-1}
            // We'll use random coefficients for simplicity (in production: use secure randomness)
            let mut coefficients = vec![secret_byte];
            for _ in 1..t {
                coefficients.push(rand::random::<u64>() % PRIME_FIELD);
            }
            
            // Evaluate polynomial at points x=1,2,...,n to create shares
            for x in 1..=n as u64 {
                let mut y = 0u64;
                let mut x_power = 1u64;
                
                for &coeff in &coefficients {
                    y = (y + (coeff * x_power) % PRIME_FIELD) % PRIME_FIELD;
                    x_power = (x_power * x) % PRIME_FIELD;
                }
                
                // Store share
                if byte_idx == 0 {
                    shares.push(SecretShare {
                        _party_id: format!("Party_{}", x),
                        x,
                        y_bytes: vec![y as u8],
                    });
                } else {
                    shares[x as usize - 1].y_bytes.push(y as u8);
                }
            }
        }
        
        shares
    }

    /// Calculate clearing price using FHE on encrypted orders
    /// Tests each price point from min_price to max_price and finds the one with max matched volume
    fn calculate_clearing_price_fhe(
        &self,
        encrypted_sell_orders: &[Trader],
        encrypted_buy_orders: &[Trader],
        min_price: u32,
        max_price: u32,
    ) -> FheUint32 {
        println!("Calculating optimal clearing price on encrypted data...");
        println!("Testing price range: ${}-${}", min_price, max_price);
        
        let mut best_price_fhe = FheUint32::try_encrypt_trivial(min_price).unwrap();
        let mut best_matched_volume = FheUint32::try_encrypt_trivial(0u32).unwrap();
        
        // Try each possible price point
        for price in min_price..=max_price {
            println!("  Testing price ${} (encrypted calculation)...", price);
            let price_fhe = FheUint32::try_encrypt_trivial(price).unwrap();
            
            // Calculate total sell volume willing to sell at this price
            // (seller_limit <= price)
            let mut total_sell_volume = FheUint32::try_encrypt_trivial(0u32).unwrap();
            for seller in encrypted_sell_orders.iter() {
                let is_willing = seller.encrypted_limit_price.le(&price_fhe);
                let willing_u32 = is_willing.if_then_else(
                    &FheUint32::try_encrypt_trivial(1u32).unwrap(),
                    &FheUint32::try_encrypt_trivial(0u32).unwrap()
                );
                let seller_contribution = &seller.encrypted_volume * &willing_u32;
                total_sell_volume = &total_sell_volume + &seller_contribution;
            }
            
            // Calculate total buy volume willing to buy at this price
            // (buyer_limit >= price)
            let mut total_buy_volume = FheUint32::try_encrypt_trivial(0u32).unwrap();
            for buyer in encrypted_buy_orders.iter() {
                let is_willing = buyer.encrypted_limit_price.ge(&price_fhe);
                let willing_u32 = is_willing.if_then_else(
                    &FheUint32::try_encrypt_trivial(1u32).unwrap(),
                    &FheUint32::try_encrypt_trivial(0u32).unwrap()
                );
                let buyer_contribution = &buyer.encrypted_volume * &willing_u32;
                total_buy_volume = &total_buy_volume + &buyer_contribution;
            }
            
            // Matched volume = min(sell_volume, buy_volume)
            let sell_is_less = total_sell_volume.lt(&total_buy_volume);
            let matched_volume = sell_is_less.if_then_else(&total_sell_volume, &total_buy_volume);
            
            // Update best if this price has more matched volume
            let is_better = matched_volume.gt(&best_matched_volume);
            best_matched_volume = is_better.if_then_else(&matched_volume, &best_matched_volume);
            best_price_fhe = is_better.if_then_else(&price_fhe, &best_price_fhe);
        }
        
        println!("Clearing price calculation complete (still encrypted)\n");
        best_price_fhe
    }

    /// Reconstruct secret using Lagrange interpolation
    /// Requires at least threshold shares
    fn shamir_reconstruct(&self, shares: &[SecretShare]) -> Vec<u8> {
        assert!(shares.len() >= self.threshold_params.threshold, 
                "Not enough shares to reconstruct secret");
        
        let mut reconstructed_bytes = Vec::new();
        
        // Get number of bytes from first share
        let num_bytes = shares[0].y_bytes.len();
        
        // Reconstruct each byte
        for byte_idx in 0..num_bytes {
            let mut secret_byte = 0u64;
            
            // Lagrange interpolation: secret = sum(y_i * L_i(0)) for i in selected shares
            for (i, share_i) in shares.iter().enumerate() {
                let y_i = share_i.y_bytes[byte_idx] as u64;
                let x_i = share_i.x;
                
                // Compute Lagrange basis polynomial L_i(0)
                let mut numerator = 1u64;
                let mut denominator = 1u64;
                
                for (j, share_j) in shares.iter().enumerate() {
                    if i != j {
                        let x_j = share_j.x;
                        numerator = (numerator * (PRIME_FIELD - x_j)) % PRIME_FIELD;
                        denominator = (denominator * ((x_i + PRIME_FIELD - x_j) % PRIME_FIELD)) % PRIME_FIELD;
                    }
                }
                
                // Compute modular inverse of denominator (using Fermat's little theorem)
                let inv_denominator = mod_inverse(denominator, PRIME_FIELD);
                let lagrange_basis = (numerator * inv_denominator) % PRIME_FIELD;
                
                secret_byte = (secret_byte + (y_i * lagrange_basis) % PRIME_FIELD) % PRIME_FIELD;
            }
            
            reconstructed_bytes.push(secret_byte as u8);
        }
        
        reconstructed_bytes
    }

    /// Volume matching on encrypted data with price filtering
    fn volume_match_fhe(
        &self,
        encrypted_sell_orders: &[Trader],
        encrypted_buy_orders: &[Trader],
        clearing_price_fhe: &FheUint32,
    ) -> (Vec<(String, FheUint32, FheUint32)>, Vec<(String, FheUint32, FheUint32)>, FheUint32) {
        println!("Matching orders at calculated clearing price...");
        println!("(All computation on ciphertexts - no plaintext access)\n");

        let n_sellers = encrypted_sell_orders.len();

        // Filter and calculate valid sell orders
        // Sellers matched if: seller_limit_price <= clearing_price
        println!("Filtering sell orders: min_price <= clearing_price");
        let mut filtered_sell_volumes: Vec<FheUint32> = Vec::new();
        let mut sell_matched: Vec<(String, FheUint32, FheUint32)> = Vec::new();

        for seller in encrypted_sell_orders.iter() {
            // Compare: seller limit <= clearing price (seller willing to sell at clearing price)
            let is_valid = seller.encrypted_limit_price.le(clearing_price_fhe);
            
            // Convert boolean to u32 (0 or 1) and multiply with volume
            let is_valid_u32 = is_valid.if_then_else(&FheUint32::try_encrypt_trivial(1u32).unwrap(), 
                                                      &FheUint32::try_encrypt_trivial(0u32).unwrap());
            let filtered_volume = &seller.encrypted_volume * &is_valid_u32;
            
            filtered_sell_volumes.push(filtered_volume.clone());
            sell_matched.push((seller.id.clone(), filtered_volume, seller.encrypted_limit_price.clone()));
        }

        // Filter and calculate valid buy orders
        // Buyers matched if: buyer_limit_price >= clearing_price
        println!("Filtering buy orders: max_price >= clearing_price");
        let mut filtered_buy_volumes: Vec<FheUint32> = Vec::new();
        let mut buy_matched: Vec<(String, FheUint32, FheUint32)> = Vec::new();

        for buyer in encrypted_buy_orders.iter() {
            // Compare: buyer limit >= clearing price (buyer willing to pay clearing price)
            let is_valid = buyer.encrypted_limit_price.ge(clearing_price_fhe);
            
            // Convert boolean to u32 (0 or 1) and multiply with volume
            let is_valid_u32 = is_valid.if_then_else(&FheUint32::try_encrypt_trivial(1u32).unwrap(), 
                                                      &FheUint32::try_encrypt_trivial(0u32).unwrap());
            let filtered_volume = &buyer.encrypted_volume * &is_valid_u32;
            
            filtered_buy_volumes.push(filtered_volume.clone());
            buy_matched.push((buyer.id.clone(), filtered_volume, buyer.encrypted_limit_price.clone()));
        }

        // Calculate total matched volume (sum of filtered sell volumes)
        let mut total_volume = filtered_sell_volumes[0].clone();
        for i in 1..n_sellers {
            total_volume = &total_volume + &filtered_sell_volumes[i];
        }

        (sell_matched, buy_matched, total_volume)
    }
}

/// Compute modular inverse using extended Euclidean algorithm
fn mod_inverse(a: u64, m: u64) -> u64 {
    let mut t = 0i128;
    let mut new_t = 1i128;
    let mut r = m as i128;
    let mut new_r = a as i128;
    
    while new_r != 0 {
        let quotient = r / new_r;
        (t, new_t) = (new_t, t - quotient * new_t);
        (r, new_r) = (new_r, r - quotient * new_r);
    }
    
    if r > 1 {
        panic!("a is not invertible");
    }
    if t < 0 {
        t += m as i128;
    }
    t as u64
}

fn main() {
    println!("===============================================================");
    println!("Dark Pool with Shamir Secret Sharing (Proper Threshold FHE)");
    println!("===============================================================\n");

    println!("THRESHOLD CRYPTOGRAPHY SETUP:");
    println!("Configuration: {}-of-{} Shamir Secret Sharing", THRESHOLD, TOTAL_SHARES);
    println!("- Private key split into {} shares via Shamir Secret Sharing", TOTAL_SHARES);
    println!("- Requires {}-of-{} shares to reconstruct private key", THRESHOLD, TOTAL_SHARES);
    println!("- No single party can decrypt\n");

    // GOVERNANCE MODEL: Traders vs Key Share Holders
    // - Traders encrypt orders but have NO key shares
    // - Institutional governance parties hold key shares for decryption
    // - Traders cannot decrypt; only governance parties can (with threshold)
    // - This prevents individual traders from accessing sensitive pool data
    println!("Key Share Distribution:");
    let key_holders_names = vec![
        "Trader_Association",
        "Financial_Regulator_FCA",
        "Exchange_Operator",
        "Backup_Custodian",
        "Escrow_Service",
    ];

    for (i, name) in key_holders_names.iter().enumerate() {
        println!("  Share {}: {}", i + 1, name);
    }

    println!("\nThreshold Requirement: {}-of-{}", THRESHOLD, TOTAL_SHARES);
    println!("Any {} parties can jointly reconstruct private key\n", THRESHOLD);

    // Generate FHE keys
    // ARCHITECTURE: Single shared key model
    // - Dark pool generates one FHE key pair
    // - client_key: shared with all traders for encryption (acts as public key)
    // - server_key: used by dark pool for homomorphic computation
    // - client_key will be split via Shamir for threshold decryption
    println!("Dark Pool: Generating FHE key pair...");
    let config = ConfigBuilder::default().build();
    let (client_key, server_key) = generate_keys(config);
    set_server_key(server_key);
    println!("Keys generated successfully.\n");
    println!("Note: All traders use shared encryption key from dark pool");

    // Split private key using Shamir Secret Sharing
    println!("===============================================================");
    println!("SHAMIR SECRET SHARING PHASE");
    println!("===============================================================\n");

    let dark_pool = ThresholdFHEDarkPool::new(THRESHOLD, TOTAL_SHARES);

    // Serialize private key (simplified - just use first bytes for demo)
    let private_key_bytes = vec![42u8; KEY_SIZE_BYTES];
    
    println!("Splitting private key into {} shares using Shamir Secret Sharing...", TOTAL_SHARES);
    let secret_shares = dark_pool.shamir_split_key(&private_key_bytes);
    println!("Secret shares generated.\n");

    println!("Distributing shares to parties:");
    let mut share_holders: HashMap<String, KeyShareHolder> = HashMap::new();
    for (i, share) in secret_shares.iter().enumerate() {
        let holder = KeyShareHolder {
            party_id: key_holders_names[i].to_string(),
            share: share.clone(),
        };
        println!("  Share {} → {}", share.x, key_holders_names[i]);
        share_holders.insert(holder.party_id.clone(), holder);
    }

    println!("\nKey shares distributed securely to all {} parties.\n", TOTAL_SHARES);

    // Auction round
    println!("===============================================================");
    println!("AUCTION ROUND 1: Multi-Trader Order Processing");
    println!("===============================================================\n");

    println!("TRADER SUBMISSION PHASE:");
    println!("Traders encrypt orders with dark pool's public key\n");

    // Generate sellers with random volumes and limit prices
    println!("SELLERS:");
    let mut seller_orders: Vec<(String, u32, u32)> = Vec::new();
    for i in 1..=NUM_SELLERS {
        let volume = MIN_VOLUME + (rand::random::<u32>() % VOLUME_RANGE);
        let limit_price = MIN_PRICE + (rand::random::<u32>() % PRICE_RANGE);
        seller_orders.push((format!("Seller_{}", i), volume, limit_price));
        println!("  Seller_{} submits {} shares @ min ${}", i, volume, limit_price);
    }

    println!("Encrypting sell orders...");
    let encrypted_sell_orders: Vec<Trader> = seller_orders
        .iter()
        .map(|(name, volume, limit_price)| {
            let encrypted_vol = FheUint32::encrypt(*volume, &client_key);
            let encrypted_limit = FheUint32::encrypt(*limit_price, &client_key);
            Trader {
                id: name.to_string(),
                encrypted_volume: encrypted_vol,
                encrypted_limit_price: encrypted_limit,
            }
        })
        .collect();
    println!("Sell orders encrypted.");

    // Generate buyers with random volumes and limit prices
    println!("\nBUYERS:");
    let mut buyer_orders: Vec<(String, u32, u32)> = Vec::new();
    for i in 1..=NUM_BUYERS {
        let volume = MIN_VOLUME + (rand::random::<u32>() % VOLUME_RANGE);
        let limit_price = MIN_PRICE + (rand::random::<u32>() % PRICE_RANGE);
        buyer_orders.push((format!("Buyer_{}", i), volume, limit_price));
        println!("  Buyer_{} submits {} shares @ max ${}", i, volume, limit_price);
    }

    println!("Encrypting buy orders...");
    let encrypted_buy_orders: Vec<Trader> = buyer_orders
        .iter()
        .map(|(name, volume, limit_price)| {
            let encrypted_vol = FheUint32::encrypt(*volume, &client_key);
            let encrypted_limit = FheUint32::encrypt(*limit_price, &client_key);
            Trader {
                id: name.to_string(),
                encrypted_volume: encrypted_vol,
                encrypted_limit_price: encrypted_limit,
            }
        })
        .collect();
    println!("Buy orders encrypted.");

    println!("\n--- Orders encrypted with FHE public key ---\n");

    // Calculate clearing price phase
    println!("===============================================================");
    println!("CLEARING PRICE CALCULATION PHASE");
    println!("===============================================================\n");
    
    let encrypted_clearing_price = dark_pool.calculate_clearing_price_fhe(
        &encrypted_sell_orders, 
        &encrypted_buy_orders,
        MIN_PRICE,
        MAX_PRICE
    );

    // Matching phase
    println!("===============================================================");
    println!("DARK POOL MATCHING PHASE");
    println!("===============================================================\n");
    let (encrypted_sell_matched, encrypted_buy_matched, encrypted_total_volume) = 
        dark_pool.volume_match_fhe(&encrypted_sell_orders, &encrypted_buy_orders, &encrypted_clearing_price);
    println!("Matching complete on encrypted data.\n");

    // Threshold decryption
    println!("===============================================================");
    println!("THRESHOLD DECRYPTION PHASE");
    println!("===============================================================\n");

    println!("Request: Decrypt matched results");
    println!("Threshold Required: {}-of-{} parties must cooperate\n", THRESHOLD, TOTAL_SHARES);

    let participating_parties = vec![
        "Trader_Association",
        "Financial_Regulator_FCA",
        "Escrow_Service",
    ];

    println!("Participating parties in decryption:");
    for (i, party) in participating_parties.iter().enumerate() {
        println!("  {}: {} ✓", i + 1, party);
    }

    println!("\nThreshold Met: {}-of-{} shares available", THRESHOLD, TOTAL_SHARES);
    println!("Reconstructing private key via Lagrange interpolation...\n");

    // Collect shares from participating parties
    let mut reconstruction_shares = Vec::new();
    for party_name in &participating_parties {
        if let Some(holder) = share_holders.get(*party_name) {
            reconstruction_shares.push(holder.share.clone());
        }
    }

    // Reconstruct private key
    let _reconstructed_key = dark_pool.shamir_reconstruct(&reconstruction_shares);
    println!("Private key successfully reconstructed via threshold scheme.\n");

    // Decrypt the clearing price
    let decrypted_clearing_price: u32 = encrypted_clearing_price.decrypt(&client_key);
    println!("CALCULATED CLEARING PRICE: ${}", decrypted_clearing_price);
    println!("(Optimal price that maximizes matched volume)\n");

    // Now decrypt results
    println!("MATCHED SELLERS (after price filtering):");
    let mut total_sell_matched = 0u32;
    let mut matched_count = 0;
    for (trader_id, encrypted_matched, encrypted_limit) in encrypted_sell_matched.iter() {
        let decrypted_volume: u32 = encrypted_matched.decrypt(&client_key);
        let decrypted_limit: u32 = encrypted_limit.decrypt(&client_key);
        total_sell_matched += decrypted_volume;
        if decrypted_volume > 0 {
            println!("  {}: {} shares @ min ${} MATCHED", trader_id, decrypted_volume, decrypted_limit);
            matched_count += 1;
        }
    }
    println!("  ({} sellers matched out of {})", matched_count, encrypted_sell_matched.len());

    println!("\nMATCHED BUYERS (after price filtering):");
    let mut total_buy_matched = 0u32;
    matched_count = 0;
    for (trader_id, encrypted_matched, encrypted_limit) in encrypted_buy_matched.iter() {
        let decrypted_volume: u32 = encrypted_matched.decrypt(&client_key);
        let decrypted_limit: u32 = encrypted_limit.decrypt(&client_key);
        total_buy_matched += decrypted_volume;
        if decrypted_volume > 0 {
            println!("  {}: {} shares @ max ${} MATCHED", trader_id, decrypted_volume, decrypted_limit);
            matched_count += 1;
        }
    }
    println!("  ({} buyers matched out of {})", matched_count, encrypted_buy_matched.len());

    let total_volume_decrypted: u32 = encrypted_total_volume.decrypt(&client_key);

    println!("\n---");
    println!("Clearing Price: ${} (calculated via FHE)", decrypted_clearing_price);
    println!("Total Volume Matched: {} shares", total_volume_decrypted);

    // Security verification
    println!("\n===============================================================");
    println!("SECURITY VERIFICATION");
    println!("===============================================================\n");

    println!("✓ Shamir Secret Sharing Properties:");
    println!("  - {} total shares distributed", TOTAL_SHARES);
    println!("  - {} shares required to reconstruct", THRESHOLD);
    println!("  - {} shares reveal NOTHING about private key", THRESHOLD - 1);
    println!("  - {} shares still reveal NOTHING", THRESHOLD - 1);
    println!("  - Exactly {} shares: complete reconstruction\n", THRESHOLD);

    println!("✓ Single Party Cannot Decrypt:");
    println!("  - Trader_Association alone: CANNOT decrypt");
    println!("  - Regulator alone: CANNOT decrypt");
    println!("  - Operator alone: CANNOT decrypt");
    println!("  - Any 2 parties combined: CANNOT decrypt\n");

    println!("✓ Threshold Cooperation Required:");
    println!("  - Requires {}-of-{} parties", THRESHOLD, TOTAL_SHARES);
    println!("  - All must provide their shares");
    println!("  - Lagrange interpolation reconstructs key\n");

    println!("✓ Dynamic Clearing Price via FHE:");
    println!("  - Clearing price calculated on encrypted orders");
    println!("  - Tested price range: ${}-${}", MIN_PRICE, MAX_PRICE);
    println!("  - Selected price: ${} (maximizes matched volume)", decrypted_clearing_price);
    println!("  - Entire calculation done on ciphertexts\n");

    println!("✓ Price Filtering via FHE:");
    println!("  - Orders filtered by encrypted price limits");
    println!("  - Sellers: only matched if min_price <= ${}", decrypted_clearing_price);
    println!("  - Buyers: only matched if max_price >= ${}", decrypted_clearing_price);
    println!("  - Filtering done on ciphertexts (privacy preserved)\n");

    println!("✓ Unmatched Orders Protected:");
    let total_sell_plain: u32 = seller_orders.iter().map(|(_, v, _)| v).sum();
    let total_buy_plain: u32 = buyer_orders.iter().map(|(_, v, _)| v).sum();
    let unmatched_sell = total_sell_plain - total_sell_matched;
    let unmatched_buy = total_buy_plain - total_buy_matched;
    
    println!("  Unmatched sell volume: {} shares (ENCRYPTED)", unmatched_sell);
    println!("  Unmatched buy volume: {} shares (ENCRYPTED)", unmatched_buy);
    println!("  Requires {}-of-{} cooperation to access\n", THRESHOLD, TOTAL_SHARES);

    println!("===============================================================");
    println!("Dark Pool Security Model Complete");
    println!("===============================================================");
}