# Halfred
~ Partial (1/2) evaluator (Reducer)

## Notes

### Partial Evaluation, Chapter 1

- `out = [[p]](i, i')`, then `p1 = [[mix]](p, i); out = [[p1]](i')`.
- Alternatively, can write as `[[p]](i, i') = [[ [[mix]](p, i) ]](i')`
- Let `S` be the source language (Early Rust). Let `T` be the target language (assembly). Let `L`
  be the language that the interpreter for `S` is implemented in (OCaml).
- See that we have the equation `out = [source]_S (in)`, or `out = [interp]_L (source, in).`
- That's the equation for the interpreter.
- a compiler produces a target program, so we have `target = [compiler]_L(source)`. Running
  the target and source programs should have the same effect, so `[target]_T(in) = [source]_S(in)`.
- Written differently, this is `[ [compiler]_L(source) ]_T(in) = [source]_S(in)`.

##### First futamura projection                          

- `out = [source]_S (in)`
- `out = [int](source, in)`
- `out = [[mix](int, source)](in)`
- But by definition of `target`, we have `out = target(in)`
- Thus, we see that `target = [mix](int, source)`. We get the *compiled output program/target program* by partially
  applying the interpreter to the source program. 

##### Second futamura projection

- Start with `target = [mix](int, source)`.
- Now partially apply, `target = [mix(mix, int)](source)`.
- But we know that `target = compiler(source)`. So we must have `[mix(mix, int)] = compiler`.
- A compiler is obtained by partially applying the partial applier against the interpreter. Thus, when
  fed an input, it partially evaluates the interpreter against any input, giving us a compiler.

#### Third futamura projection

- consider `cogen = [mix(mix, mix)]`, applied to an interpreter.
- Let `comp = cogen(interp) = ([mix](mix, mix))(interp) = mix(mix, interp)`
- Apply `comp(source)`. This gives us `comp(source) = mix(mix, interp)(source) = mix(interp, source) = target`.
- Thus, we have create a compiler generator, which takes an interpreter and produces a compiler.

### Partial Evaluation, Chapter 3

#### Bootstrapping and self-application

- Suppose we have a high-level compiler in the language `S`, from `S` to `T`. I will denote that as `h : S(S → T)`.
  where the compiler is `h` (for high), written in language `S`, from `S` to `T`.
- We also have a low-level compiler written in `T` from `S` to `T`, denoted by
  `l : T(S → T)`, where the compiler is `l` for low.
- Suppose the two versions agree, so `[h]_S = [l]_T`.
- Suppose we extend `h` to `h'`, to compile the
   language `S'` to `T`. `h'` is also written in `S`, so we have `h': S(S'→ T)`.
- Now we can use `t` on `h'` to recieve an `S'` compiler `l' : T(S' → T)`.
- We continue this process, to arrive at the following equations:

- The above equations is more easily understood via ASCII art:

- This shows how one can bootstrap/self-apply a compiler, and these types of diagrams
  will help us reason about self application later on, in the context of partial application.

## References

- Partial evaluation and automatic program generation by Neil D Jones,
  Carsten K Gomard and Peter Setsoft

