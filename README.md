### A tiny PLookup implementation.

This project is based on [TyPLONK](https://github.com/fabrizio-m/TyPLONK) and extends it with lookup implementation. The Loopup implementation is inspired by [理解 PLONK（七）：Lookup Gate](https://github.com/sec-bit/learning-zkp/blob/master/plonk-intro-cn/7-plonk-lookup.md) and [PlonKup: Reconciling PlonK with plookup](https://eprint.iacr.org/2022/086)

**Note:** The project only implements the lookup feature and has not yet integrated it with PLONK. The implementation can be found in `plonk\src\single_lookup.rs`

#### Usecase:

```rust
fn test_lookup_table() {
    let mut table = LookupTable::new(vec![2, 3, 4]);
    let mut f_table = FTable::new();
    f_table.add_table(vec![2, 3]);

    let proof = table.prove(f_table);
    table.verify(proof);
}
```
Here `f_table` contains the data you want to prove is in the lookup table.
