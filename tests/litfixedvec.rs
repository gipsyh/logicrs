use logicrs::{DagCnf, LitFixedVec, LitVec, Var};

#[test]
fn fixed_literals_own_their_allocation() {
    assert_eq!(size_of::<LitFixedVec>(), size_of::<usize>());
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<LitFixedVec>();

    for len in [0, 1, 2, 3, 4, 257, 4096] {
        let original: LitVec = (0..len).map(|i| Var::new(i).lit()).collect();
        let mut fixed = LitFixedVec::from(original.clone());
        assert_eq!(fixed.as_slice(), original.as_slice());
        assert_eq!(fixed.mem_usage(), if len == 0 { 0 } else { 4 * (len + 1) });
        let cloned = fixed.clone();
        if len > 0 {
            assert_ne!(fixed.as_ptr(), cloned.as_ptr());
            fixed[0] = !fixed[0];
            fixed.reverse();
        }
        drop(fixed);
        let moved = std::thread::spawn(move || LitVec::from(cloned))
            .join()
            .unwrap();
        assert_eq!(moved, original);
    }
}

fn sample_dag() -> DagCnf {
    let mut dag = DagCnf::new();
    let a = dag.new_var().lit();
    let b = dag.new_var().lit();
    let and = dag.new_and([a, b]);
    dag.new_xor(and, a);
    dag
}

#[test]
fn dag_conversion_preserves_clauses_and_ownership() {
    let dag = sample_dag();
    let expected = dag.lower();
    let pointers: Vec<_> = dag.clause().map(|c| c.as_ptr()).collect();
    let max_var = dag.max_var();
    let mut flat = dag.into_cnf();
    assert_eq!(flat.max_var(), max_var);
    assert_eq!(flat.clauses(), expected.clauses());
    assert_eq!(
        flat.iter().map(|c| c.as_ptr()).collect::<Vec<_>>(),
        pointers
    );
    let clauses = flat.take_clauses();
    assert!(flat.is_empty());
    flat.set_cls(clauses);
    assert_eq!(flat.clauses(), expected.clauses());
}
