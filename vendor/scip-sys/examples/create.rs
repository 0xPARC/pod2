use std::ffi::CString;
use scip_sys::*;
use std::mem::MaybeUninit;

fn main() {
    let mut scip_ptr = MaybeUninit::uninit();
    unsafe { SCIPcreate(scip_ptr.as_mut_ptr()) };
    let mut scip_ptr = unsafe { scip_ptr.assume_init() };

    // include default plugins
    unsafe { SCIPincludeDefaultPlugins(scip_ptr) };

    unsafe { SCIPcreateProbBasic(scip_ptr, CString::new("test").unwrap().as_ptr()) };

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
}
