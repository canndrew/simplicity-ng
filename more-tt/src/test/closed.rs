use crate::priv_prelude::*;

#[test]
fn test() {
    closed::symmetry::<StringScheme>();
    closed::transitivity::<StringScheme>();
    closed::heterogeneous_equal::<StringScheme>();
    closed::heterogeneous_transitivity::<StringScheme>();
    closed::congruence::<StringScheme>();
    closed::equality_contractible::<StringScheme>();
    closed::cong::<StringScheme>();
    closed::fold::<StringScheme>();
    closed::sigma_eq_cong::<StringScheme>();
    closed::pi_eq_cong::<StringScheme>();
    closed::case_eq::<StringScheme>();
    closed::pair_eq::<StringScheme>();
    closed::equals_refl::<StringScheme>();

    for n in 0..5 {
        closed::congruence_multi::<StringScheme>(n);
    }
}

