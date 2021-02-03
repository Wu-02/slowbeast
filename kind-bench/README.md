## Benchmarks for k-induction

### Legend to names of benchmarks

Every benchmark contains one or more loops without nesting
and are named as follows:

    ([ms]p_(a[ai])?)^*[-bug?]-id

mp/sp - multi-path, single-path
ai/aa - assertion inside, assertion after
bug   - present if some assertion may be violated
id is some identifier of the benchmark

For example:

mp_aa-1.c  - one multi-path loop with assertion after
sp-mp_ai-1.c  - one single-path loop followed by multi-path loop with assertion inside


### Nested loop benchmarks

TBD
