// TODO: Move the MainPod logic to mock_main and implement the MainPod trait
/*
use anyhow::Result;
use itertools::Itertools;
use plonky2::field::types::{Field, PrimeField64};
use std::collections::HashMap;
use std::io::{self, Write};
use std::iter;

use crate::merkletree::MerkleTree;
use crate::middleware::{Hash, Params, PodId, Value, NULL};

pub struct Printer {
    pub skip_none: bool,
}

impl Printer {
    pub fn fmt_arg(&self, w: &mut dyn Write, arg: &StatementArg) -> io::Result<()> {
        match arg {
            StatementArg::None => write!(w, "none"),
            StatementArg::Literal(v) => write!(w, "{}", v),
            StatementArg::Ref(r) => write!(w, "{}.{}", r.0, r.1),
        }
    }

    pub fn fmt_signed_pod(&self, w: &mut dyn Write, pod: &SignedPod) -> io::Result<()> {
        writeln!(w, "SignedPod ({}):", pod.id)?;
        // Note: current version iterates sorting by keys of the kvs, but the merkletree defined at
        // https://0xparc.github.io/pod2/merkletree.html will not need it since it will be
        // deterministic based on the keys values not on the order of the keys when added into the
        // tree.
        for (k, v) in pod.kvs.iter().sorted_by_key(|kv| kv.0) {
            writeln!(w, "  - {}: {}", k, v)?;
        }
        Ok(())
    }

    pub fn fmt_statement(&self, w: &mut dyn Write, st: &Statement) -> io::Result<()> {
        write!(w, "{:?} ", st.0)?;
        for (i, arg) in st.1.iter().enumerate() {
            if !(self.skip_none && arg.is_none()) {
                if i != 0 {
                    write!(w, " ")?;
                }
                self.fmt_arg(w, arg)?;
            }
        }
        Ok(())
    }

    pub fn fmt_statement_index(
        &self,
        w: &mut dyn Write,
        st: &Statement,
        index: usize,
    ) -> io::Result<()> {
        if !(self.skip_none && st.is_none()) {
            write!(w, "    {:03}. ", index)?;
            self.fmt_statement(w, &st)?;
            write!(w, "\n")?;
        }
        Ok(())
    }

    pub fn fmt_main_pod(&self, w: &mut dyn Write, pod: &MainPod) -> io::Result<()> {
        writeln!(w, "MainPod ({}):", pod.id)?;
        // TODO
        // writeln!(w, "  input_main_pods:")?;
        // for in_pod in &pod.input_main_pods {
        //     writeln!(w, "    - {}", in_pod.id)?;
        // }
        let mut st_index = 0;
        for (i, (pod, statements)) in pod
            .input_signed_pods
            .iter()
            .zip(pod.input_signed_pods_statements())
            .enumerate()
        {
            if !(self.skip_none && pod.is_null()) {
                writeln!(w, "  in sig_pod {:02} (id:{}) statements:", i, pod.id)?;
                for st in statements {
                    self.fmt_statement_index(w, &st, st_index)?;
                    st_index += 1;
                }
            } else {
                st_index += pod.params.max_signed_pod_values;
            }
        }
        writeln!(w, "  prv statements:")?;
        for st in pod.prv_statements() {
            self.fmt_statement_index(w, &st, st_index)?;
            st_index += 1;
        }
        writeln!(w, "  pub statements:")?;
        for st in pod.pub_statements() {
            self.fmt_statement_index(w, &st, st_index)?;
            st_index += 1;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend;

    #[test]
    fn test_back_0() -> Result<()> {
        let params = Params::default();
        let (front_gov_id, front_pay_stub, front_kyc) = frontend::tests::data_zu_kyc(params)?;
        let gov_id = front_gov_id.pod; // get backend's pod
        let pay_stub = front_pay_stub.pod; // get backend's pod
        let kyc = front_kyc.compile()?;
        // println!("{:#?}", kyc);

        let printer = Printer { skip_none: true };
        let mut w = io::stdout();
        printer.fmt_signed_pod(&mut w, &gov_id)?;
        printer.fmt_signed_pod(&mut w, &pay_stub)?;
        printer.fmt_main_pod(&mut w, &kyc)?;

        Ok(())
    }
}
*/
