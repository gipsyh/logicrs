use logicrs::{DagCnf, Lit, LitVec, Var, simplify::DagCnfSimplify};
use std::collections::BTreeSet;

// Existentially quantify unfrozen variables and compare the truth tables over
// the observable variables. BVE may remove internal gate variables entirely.
fn projected_models(dag: &DagCnf, frozen: &[Var]) -> BTreeSet<u32> {
    let mask = frozen.iter().fold(0, |mask, v| {
        if v.is_constant() {
            mask
        } else {
            mask | (1 << (v.0 - 1))
        }
    });
    (0..1 << dag.max_var().0)
        .filter(|bits| {
            dag.clause().all(|clause| {
                clause.iter().any(|l| {
                    // Variable zero denotes false; Lit::TRUE negates it.
                    let value = !l.var().is_constant() && bits & (1 << (l.var().0 - 1)) != 0;
                    value == l.polarity()
                })
            })
        })
        .map(|bits| bits & mask)
        .collect()
}

#[test]
fn simplifying_fixed_clauses_preserves_projected_models() {
    for seed in 0..16 {
        let mut dag = DagCnf::new();
        let a = dag.new_var().lit();
        let b = dag.new_var().lit();
        let c = dag.new_var().lit();
        let and = dag.new_and([a.not_if(seed & 1 != 0), b]);
        let xor = dag.new_xor(and, c.not_if(seed & 2 != 0));
        let or = dag.new_or([and, !xor]);
        let root = dag.new_ite(a, or.not_if(seed & 4 != 0), xor.not_if(seed & 8 != 0));
        for frozen in [
            vec![a.var(), b.var(), c.var(), root.var()],
            dag.var_iter().collect(),
        ] {
            let expected = projected_models(&dag, &frozen);
            assert_eq!(expected.len(), 8);
            let owned = dag.clone().simplify(frozen.iter().copied());
            assert_eq!(
                projected_models(&owned, &frozen),
                expected,
                "owned, seed {seed}"
            );

            let mut borrowed = DagCnfSimplify::new(&dag);
            for &v in &frozen {
                borrowed.froze(v);
            }
            let result = borrowed.simplify();
            assert_eq!(
                projected_models(&result, &frozen),
                expected,
                "borrowed, seed {seed}"
            );
        }
    }
}

#[test]
fn simplifier_deduplicates_and_strengthens_fixed_clauses() {
    let mut dag = DagCnf::new();
    let a = dag.new_var().lit();
    let b = dag.new_var().lit();
    let n = dag.new_var().lit();
    // Resolving the first two clauses strengthens them to [a, n]; the
    // duplicate and subsumed clauses exercise deletion and in-place retain.
    dag.add_rel(
        n.var(),
        &[
            LitVec::from([a, b, b, n]),
            LitVec::from([a, !b, n]),
            LitVec::from([a, b, n]),
        ],
    );
    let frozen: Vec<_> = dag.var_iter().collect();
    let expected = projected_models(&dag, &frozen);
    assert_eq!(expected.len(), 6);
    let mut simplifier = DagCnfSimplify::from_owned(dag);
    for &v in &frozen {
        simplifier.froze(v);
    }
    simplifier.subsume_simplify();
    let result = simplifier.finalize();
    assert_eq!(projected_models(&result, &frozen), expected);
    assert!(result[n.var()].iter().any(|c| c.as_slice() == [a, n]));
}

#[test]
fn simplifier_propagates_constants_with_fixed_clauses() {
    let mut dag = DagCnf::new();
    let a = dag.new_var();
    dag.add_rel(a, &[LitVec::from([a.lit()])]);
    let b = dag.new_var().lit();
    let and = dag.new_and([a.lit(), b]);
    let root = dag.new_and([!a.lit(), and]);
    let frozen: Vec<_> = dag.var_iter().collect();
    let expected = projected_models(&dag, &frozen);
    let simplified = dag.simplify(frozen.iter().copied());
    assert_eq!(projected_models(&simplified, &frozen), expected);
    assert!(
        simplified[root.var()]
            .iter()
            .any(|c| c.as_slice() == [!root])
    );
    assert_eq!(expected.len(), 2);
    assert!(simplified[Var::CONST][0].as_slice() == [Lit::TRUE]);
}
