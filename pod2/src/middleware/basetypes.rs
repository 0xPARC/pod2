//! This file exposes the backend dependent basetypes as middleware types,
//! taking them from the feature-enabled backend.
//!
//! This is done in order to avoid inconsistencies where a type or parameter is
//! defined in the middleware to have certain carachteristic and later in the
//! backend it gets used differently. The idea is that those types and
//! parameters (eg. lengths) have a single source of truth in the code; and in
//! the case of the "base types" this is determined by the backend being used
//! under the hood, not by a choice of the middleware parameters.
//!
//! The idea with this approach, is that the frontend & middleware should not
//! need to import the proving library used by the backend (eg. plonky2,
//! plonky3, etc).
//!
//! For example, the `Hash` and `Value` types are types belonging at the
//! middleware, and is the middleware who reasons about them, but depending on
//! the backend being used, the `Hash` and `Value` types will have different
//! sizes. So it's the backend being used who actually defines their nature
//! under the hood. For example with a plonky2 backend, these types will have a
//! length of 4 field elements, whereas with a plonky3 backend they will have a
//! length of 8 field eleements.
//!
//! Note that his approach does not introduce new traits or abstract code,
//! just makes use of rust features to define 'base types' that are being used
//! in the middleware.
//!
//!
//! NOTE (TMP): current implementation still uses plonky2 in the middleware for
//! u64/i64 to F conversion. Eventually we will do those conversions through the
//! approach described in this file, removing the imports of plonky2 in the
//! middleware.

/// Value, Hash and F are imported based on 'features'. For example by default
/// we use the 'plonky2' feature, but it could be used a 'plonky3' feature, so
/// then the Value, Hash and F types would come from the plonky3 backend.
#[cfg(feature = "backend_plonky2")]
pub use crate::backends::plonky2::basetypes::{
    hash_fields, hash_str, hash_value, Hash, Value, EMPTY_HASH, EMPTY_VALUE, F, HASH_SIZE,
    SELF_ID_HASH, VALUE_SIZE,
};
