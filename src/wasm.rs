use wasm_bindgen::prelude::*;
use crate::lang::parse;
use crate::middleware::Params;

#[wasm_bindgen(start)]
pub fn init() {
    console_error_panic_hook::set_once();
}

#[wasm_bindgen]
pub fn validate_podlang(input: &str) -> String {
    let params = Params::default();
    
    match parse(input, &params, &[]) {
        Ok(result) => {
            let predicates = result.custom_batch.predicates();
            let predicate_names: Vec<String> = predicates
                .iter()
                .map(|p| p.name.to_string())
                .collect();
            
            format!(
                "✓ Valid PODlang!\n\nFound {} predicate(s):\n{}",
                predicates.len(),
                predicate_names.join("\n")
            )
        }
        Err(e) => {
            format!("✗ Parse Error:\n{}", e)
        }
    }
}
