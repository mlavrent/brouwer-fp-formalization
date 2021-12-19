# Brouwer Fixed point theorem

## Background

The Brouwer fixed point theorem asserts that any function `f : D² → ∂D²` i.e. from the disk to its boundary has a fixed point. This result is proved using the no retraction theorem, which asserts that there is no continuous retract from the disk to its boundary. Brouwer follows quickly from that, since given a function with no fixed points, we can construct a retraction, which gives us a contradiction.

The no retraction theorem is proved by observing that the fundamental group `π₁(D²) = 0` but `π₁(∂D²) = π₁(S¹) = ℤ`. Since retractions are surjective, so is the induced homomorphism. However, we then have a contradiction since it's impossible to have a surjective homomorphism 0 → ℤ.

## What needed to be done
Mathlib has surprisingly little on the fundamental group. Below is a list of definitions and theorems that needed to be built up in order to prove Brouwer.

- define a pointed space i.e. a space with a distinguished basepoint
  - define a pointed map i.e. a continuous map between pointed spaces that maps the domain's basepoint to the codomain's
- define the fundamental group (as the automorphism group at the basepoint of the fundamental groupoid) of a pointed space
  - prove that a path connected space has the same (isomorphic) fundamental group regardless of the choice of basepoint
  - define the functor on fundamental groupoids induced by a pointed map between spaces
  - defined the induced homomorphism on fundamental groups induced by a pointed map between spaces using this functor
  - prove that if the original pointed map is surjective, the induced homomorphism is as well
- define a retraction
  - prove retractions are surjective
  - compute the fundamental group of the circle and the disk
  - prove there is no surjective homomorphism 0 → ℤ (and thus none between the fundamental groups of the disk and the circle)
  - prove the no retraction theorem
- prove the Brouwer fixed point theorem
  - define the induced retraction by the non-fixed point map
  - derive a contradiction with the no retraction theorem

## Goal status
- Pointed spaces & maps are completely defined and helper lemmas were proved
- Pointed spaces for the disk, its boundary and the circle were defined
  - other helper lemmas such as the equivalence of ∂D² and S¹ were proved

- fundamental group defined & proven to be a group
  - proved irrelevance of basepoint in path connected spaces
  - defined the induced functor on fundamental groupoids
    - still need to show that it treats composition correctly
  - defined induced homomorphism on fundamental groups
    - still need to show map_one and map_mul (these shoul follow from the map_comp property of the induced functor)

  - need to prove that a surjective map induces a surjective homomorphism (the outline is there, just needs to be filled in)

- no retraction theorem : proved
  - just need to compute the fundamental group of the disk and the circle