A formalization of the Dedekind real numbers in Coq.

The formalization started as a student project at the University of Ljubljana.
At this point the formalization is unfinished (search for `todo` in the Coq
files). We would be delighted by contributions that would bring the formalization
closer to completeion.

#### Compilation instruction

A fairly recent version of Coq should do. Run `make` to compile the files:

* `make` -- to compile
* `make all` -- to make all that is to be made
* `make clean` -- to remove the compiled files
* `make html` -- to make the HTML documentation
* `make install` -- we have never tried to run this

#### Structure of the modules

* `MiscLemmas`: various lemmas about rational numbers
* `Cut`: definition of Dedekind cuts and several other basic notions
* `Additive`: Additive structure of the reals
* `Multiplication` : Multiplicative structure of the relas
* `Order` : The order on the reals
* `Archimedean`: the proof that the reals satisfy the archimedean property
* `Completeness`: the reals are Dedekind-complete
