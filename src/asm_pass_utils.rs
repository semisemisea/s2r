use crate::riscv_utils::List;

pub trait AsmPass {
    fn run_on(&self, insts: &mut List);
}

pub struct AsmPassManager {
    passes: Vec<Box<dyn AsmPass>>,
}

impl AsmPassManager {
    pub fn run_passes(&self, insts: &mut List) {
        self.passes.iter().for_each(|pass| pass.run_on(insts));
    }

    pub fn register(&mut self, pass: Box<dyn AsmPass>) {
        self.passes.push(pass);
    }

    pub fn new() -> AsmPassManager {
        Self { passes: Vec::new() }
    }
}
