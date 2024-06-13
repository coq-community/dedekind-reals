<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Dedekind Reals

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/dedekind-reals/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/dedekind-reals/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



A formalization of Dedekind reals numbers that started as a
student project at the University of Ljubljana under the supervision
of Andrej Bauer, and was brought to the present state by Vincent Semeria.

At this point the formalization of the field of reals is finished.
There are still several unfinished theorems concering the lattice-theoretic
structure of the reals (search for `todo` in the Coq files). We would be
delighted by contributions that would bring the formalization
closer to completion.

## Meta

- Author(s):
  - Andrej Bauer
  - Vincent Semeria
- Coq-community maintainer(s):
  - Andrej Bauer ([**@andrejbauer**](https://github.com/andrejbauer))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.16 and later
- Additional dependencies: none
- Coq namespace: `DedekindReals`
- Related publication(s): none

## Building instructions

To build and install, do:

```shell
git clone https://github.com/coq-community/dedekind-reals.git
cd dedekind-reals
make   # or make -j <number-of-cores-on-your-machine> 
make install
```

## Structure of the modules

- `MiscLemmas`: various lemmas about rational numbers
- `Cut`: definition of Dedekind cuts and several other basic notions
- `Additive`: Additive structure of the reals
- `Multiplication` : Multiplicative structure of the relas
- `Order` : The order on the reals
- `Archimedean`: the proof that the reals satisfy the archimedean property
- `Completeness`: the reals are Dedekind-complete
