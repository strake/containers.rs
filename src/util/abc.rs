use quickcheck as qc;
use rand::Rng;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ABC { A, B, C }

use self::ABC::*;

impl qc::Arbitrary for ABC {
    fn arbitrary<G: qc::Gen>(g: &mut G) -> Self {
        match g.gen_range(0u8, 3) { 0 => A, 1 => B, _ => C }
    }
}
