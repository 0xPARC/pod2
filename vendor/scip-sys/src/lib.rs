//! This crate exposes automatically generated raw bindings to [SCIP](https://scipopt.org/)'s C-API. The documentation is automatically generated from the C-API docs, for further info please refer to SCIP's original [documentation](https://scipopt.org/doc/html/).

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(improper_ctypes)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;
    use std::mem::MaybeUninit;

    #[test]
    fn test_create() {
        let mut scip_ptr = MaybeUninit::uninit();
        unsafe { SCIPcreate(scip_ptr.as_mut_ptr()) };
        let mut scip_ptr = unsafe { scip_ptr.assume_init() };

        // include default plugins
        unsafe { SCIPincludeDefaultPlugins(scip_ptr) };

        let name = CString::new("test").unwrap();
        unsafe { SCIPcreateProbBasic(scip_ptr, name.as_ptr()) };

        // add a variable
        let mut var_ptr = MaybeUninit::uninit();
        unsafe {
            SCIPcreateVarBasic(
                scip_ptr,
                var_ptr.as_mut_ptr(),
                CString::new("x").unwrap().as_ptr(),
                0.0,
                1.0,
                1.0,
                SCIP_Vartype_SCIP_VARTYPE_BINARY,
            )
        };
        let mut var_ptr = unsafe { var_ptr.assume_init() };
        unsafe { SCIPaddVar(scip_ptr, var_ptr) };

        // add a constraint
        let mut cons_ptr = MaybeUninit::uninit();
        unsafe {
            SCIPcreateConsBasicLinear(
                scip_ptr,
                cons_ptr.as_mut_ptr(),
                CString::new("c").unwrap().as_ptr(),
                1,
                &mut var_ptr,
                &mut 1.0,
                1.0,
                1.0,
            )
        };
        let mut cons_ptr = unsafe { cons_ptr.assume_init() };
        unsafe { SCIPaddCons(scip_ptr, cons_ptr) };

        unsafe { SCIPsolve(scip_ptr) };

        let obj_val = unsafe { SCIPgetPrimalbound(scip_ptr) };
        let eps = unsafe { SCIPfeastol(scip_ptr) };
        assert!((obj_val - 1.0).abs() < eps);

        unsafe { SCIPreleaseVar(scip_ptr, &mut var_ptr) };
        unsafe { SCIPreleaseCons(scip_ptr, &mut cons_ptr) };
        unsafe { SCIPfree(&mut scip_ptr) };
        // Get some constants defined in def.h
        println!("Found SCIP_INVALID: {}", SCIP_INVALID);
    }
}
