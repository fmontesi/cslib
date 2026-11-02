**Table of Contents**

- [Contributing to CSLib](#contributing-to-cslib)
- [Contribution model](#contribution-model)
- [The role of AI](#the-role-of-ai)
- [Principles and Coding Style](#principles-and-coding-style)
- [Continuous Integration](#continuous-integration)
  - [Pull Request Titles](#pull-request-titles)
  - [Testing](#testing)
  - [Linting](#linting)
  - [Imports](#imports)
- [Getting started](#getting-started)
  - [Before you start: coordination to avoid rework](#before-you-start-coordination-to-avoid-rework)
  - [Finding tasks](#finding-tasks)
  - [Working groups](#working-groups)
    - [Proposing a new working group](#proposing-a-new-working-group)
  - [Examples of welcome contributions](#examples-of-welcome-contributions)
    - [Pillar 1: Formalising Computer Science in Lean](#pillar-1-formalising-computer-science-in-lean)
      - [Algorithms and Data Structures](#algorithms-and-data-structures)
        - [Verified data structures with time complexity (Batteries + Time Monad)](#verified-data-structures-with-time-complexity-batteries--time-monad)
        - [Graph algorithms and graph foundations](#graph-algorithms-and-graph-foundations)
        - [APIs for algorithmic paradigms](#apis-for-algorithmic-paradigms)
      - [Programming Languages, Models of Computation and Interaction](#programming-languages-models-of-computation-and-interaction)
      - [Logics](#logics)
      - [Semantics and program equivalences](#semantics-and-program-equivalences)
        - [Semantic frameworks](#semantic-frameworks)
        - [Program equivalences](#program-equivalences)
    - [Pillar 2: Code reasoning](#pillar-2-code-reasoning)
      - [Contributing Boole examples](#contributing-boole-examples)
      - [Boole specifications](#boole-specifications)
      - [Issue labels for Boole](#issue-labels-for-boole)
      - [Front ends for Boole](#front-ends-for-boole)
      - [Back ends for Boole](#back-ends-for-boole)
      - [Implementing verification paradigms](#implementing-verification-paradigms)
      - [Lean automation](#lean-automation)

# Contributing to CSLib

It's great that you're interested in contributing to CSLib! :tada:

Please read the rest of this document before submitting a pull request.
If you have any questions, a good place to ask them is the [Lean prover Zulip chat](https://leanprover.zulipchat.com/).

# Contribution model

To get your code approved, you need to submit a [pull request (PR)](https://github.com/leanprover/cslib/pulls).
Each PR needs to be approved by at least one maintainer.
For more details on the decision making process about PRs, please see [pull request inclusion](/DECISION_MAKING.md#pull-request-inclusion).
You can also read the [list of current maintainers](/GOVERNANCE.md#maintainers).

If you are adding something new to CSLib and are in doubt about it, you are very welcome to contact us on the [Lean prover Zulip chat](https://leanprover.zulipchat.com/).

If you are unfamiliar with CSLib as a whole and want to understand how to get started, please see [Getting started](#getting-started).

For a more detailed explanation of CSLib's decision-making processes, see [decision making](/DECISION_MAKING.md).

# The role of AI

CSLib in general follows the Mathlib policy on [use of AI](https://leanprover-community.github.io/contribute/index.html#use-of-ai). In particular, take note of:
> If you use artificial intelligence [...] please explain this in the PR description. Explain which tool(s) you used and how you used it. This provides useful context for reviewers: tools make different mistakes than humans, so knowing this makes it easier to spot common errors.

# Principles and Coding Style

Please refer to [CODESTYLE](/CODESTYLE.md).

# Continuous Integration

There are a number of checks that run in continuous integration. Here is a brief guide that includes
instructions on how to run these locally.

Adaptations for upcoming Lean releases are developed in
[downstream-lean4](https://github.com/leanprover/downstream-lean4).
Its export PRs target CSLib's current `bump/v4.X.0` branch and use the corresponding Mathlib bump branch.
Contribute adaptations in `downstream-lean4` and review the exported PRs in CSLib.

## Pull Request Titles

It is required that pull request titles begin with one of the following categories followed by a
colon: `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`. These may optionally be followed by a
parenthetical containing what area of the library the PR is working on.

## Testing

There is a series of tests that runs for each PR. The components of this are

- running the tests found in [CslibTests](/CslibTests)
- checking that all files import [Cslib.Init](/Cslib/Init.lean), which sets up some default linting
  and tactics

You can run these locally with `lake test` and `lake exe checkInitImports` respectively.

## Linting

CSLib uses a number of linters, mostly inherited from Batteries and Mathlib. These come in two varieties:

- *syntax linters*, which appear as you write your code and will give warnings in `lake build`
- *environment linters*, which can be run using `lake lint` or the `#lint` command

## Imports

There is also a test that [Cslib.lean](/Cslib.lean) imports all files. You can ensure this by
running `lake exe mk_all` locally, which will make the required changes.

CSLib tests for minimized imports using `lake shake --add-public --keep-implied --keep-prefix`, which also comes with a `--fix` option.
See `lake shake --help` for the special comment syntax used to preserve imports required for tactics or typeclasses.

# Getting started

CSLib is a community effort. To understand its scope and vision, please read the [CSLib whitepaper](https://arxiv.org/abs/2602.04846).
For an overview of its technical approach to reuse, continuous integration, and proof automation, please read the [Computer Science as Infrastructure paper](https://arxiv.org/abs/2602.15078).

Key project links include:

- Website: https://www.cslib.io/
- GitHub issues + PRs: https://github.com/leanprover/cslib
- Open contribution board: https://github.com/leanprover/cslib/projects?query=is%3Aopen
- Community discussion (Lean Community Zulip): https://leanprover.zulipchat.com/
  - CSLib channels are the recommended place to coordinate and ask questions.

## Before you start: coordination to avoid rework

Most contributions are welcome as straightforward PRs. However, **for any major development**, it is strongly recommended to discuss first on Zulip (or via a GitHub issue) so that the scope, dependencies, and placement in the library are aligned.

Examples of work that should be discussed first:

- New cross-cutting abstractions / typeclasses / notation schemes.
- New foundational frameworks.
- Major refactorings.
- New frontend or backend components for CSLib's verification infrastructure.
- Proposals for new working groups (see below).

## Finding tasks

If you are looking for a concrete starting point, please look at:

- The CSLib Zulip channels.
- Our [GitHub issues](https://github.com/leanprover/cslib/issues).

## Working groups

CSLib is structured to support multiple topic-focused efforts. We organise sustained work via **working groups** (informal or formal), which typically have a topic scope and a Zulip topic/channel for coordination.

If you want to **join** a working group, start by posting on the relevant CSLib Zulip channel describing your background and what you want to contribute.

### Proposing a new working group

If you want to propose a new working group, write a short proposal (Zulip message or GitHub issue is fine) that includes:

- **Topic**: What do you want to do?
- **Execution plan**: What is your execution plan?
- **Collaborators**: If some group or people are already planning to work on the topic, write them.

The goal is to keep proposals lightweight while ensuring CSLib remains coherent and reusable.

## Examples of welcome contributions

Here you can find some (non-exhaustive) examples of topics looking for contributions.

### Pillar 1: Formalising Computer Science in Lean

Pillar 1 is about the formalisation of Computer Science as reusable infrastructure. This includes, but is not limited to, models of computation, semantics, logics, algorithms, data structures, metatheory, and supporting mathematics.

#### Algorithms and Data Structures

##### Verified data structures with time complexity (Batteries + Time Monad)

A concrete and high-impact track is to verify implementations and time complexity bounds for [data structures from Batteries](https://github.com/leanprover-community/batteries/tree/main/Batteries/Data).

Examples of candidate targets:

- List and Array developments
- Binary heap
- Binomial heap
- Union find
- Red-black trees

##### Graph algorithms and graph foundations

- Foundational definitions (directed/undirected simple graphs, etc.)
- Core algorithms and their correctness proofs:
  - DFS, topological sorting, SCC
  - shortest paths, APSP
  - max-flow
  - minimum spanning tree
  - spanners
  - Gomory–Hu trees

##### APIs for algorithmic paradigms

Reusable APIs that support many concrete algorithms.

- Divide-and-conquer
  - Master theorem
- Dynamic programming
  - generic DP API patterns
  - quadrangle inequality (Yao ’80)
  - SMAWK algorithm

#### Programming Languages, Models of Computation and Interaction

- Automata (on finite and infinite words)
- Choreographic languages
- Lambda calculi
- Petri Nets
- Process calculi, like CCS and pi-calculus
- Frameworks for language encodings (compilers, etc.).
- Proof techniques for the correctness of encodings.

#### Logics

We aim at formalising a number of logics of different kinds, including linear logic, modal logics, etc.

We welcome proofs of logical equivalences and metatheoretical results such as identity expansion, cut elimination, etc.

Examples of interesting logics include:
- Linear logic
- Temporal logic
- Separation logic

#### Semantics and program equivalences

##### Semantic frameworks
- Denotational semantics
- Operational semantics, including results on labelled transition systems and reduction systems

##### Program equivalences

- Bisimulation
- May/Must testing
- Trace equivalence

### Pillar 2: Code reasoning

Pillar 2 is about infrastructure for reasoning about code in mainstream programming languages via intermediate representations, VC generation, and automation.

We are interested in collecting a large number of programs in Boole (see the [CSLib whitepaper](https://arxiv.org/abs/2602.04846) for Boole's vision).

You can try the Boole sandbox examples at <https://github.com/leanprover/cslib/tree/Boole-sandbox/Cslib/Languages/Boole>.

#### Contributing Boole examples

We are interested in collecting a large number of programs in Boole.

If you'd like to contribute examples, please propose and coordinate on the [Zulip channel for code reasoning](https://leanprover.zulipchat.com/#narrow/channel/563135-CSLib.3A-Code-Reasoning) first (especially if the example requires new features).

We separate Boole examples into two directories:

- examples that work with the current Boole back end
- examples that are broken or contain features not yet implemented

Contributions to both sets are valuable: working examples demonstrate capabilities; 'broken' examples identify missing features and bottlenecks.

#### Boole specifications

Currently, Boole specifications are based on Strata Core: <https://strata-org.github.io/Strata/>

A key long-term goal is to support specifications that reference arbitrary Lean concepts, especially those formalised as part of CSLib Pillar 1. Designing this cleanly within the Strata framework is a challenging and valuable project.

#### Issue labels for Boole

If you have feature requests for Boole, file an issue with title `feat(Boole): <feature request title here>`.

For bugs, errors, or other issues, file an issue with label `Boole`.

#### Front ends for Boole

We are interested in developing translations from real-world programming languages to Boole.

- Prototype translations are welcome to explore feasibility and identify design constraints.
- If you want to propose a translation for inclusion in CSLib, coordinate on Zulip.

We expect initial translations will be ad hoc and trusted. The eventual goal is to formalize the semantics of front ends and prove (as a Lean metatheorem) that translations preserve semantics.

#### Back ends for Boole

We are interested in building Boole back ends that take as input Boole programs with formal specifications and construct proof obligations in Lean, which, if proved, ensure that the program meets its specification.

- A prototype translation based on a deep embedding in Strata exists, but is not fully foundational.
- A major long-term goal is to prove Lean meta-theorems showing that proving the verification conditions ensures correctness of the Boole program.

Alternative directions are welcome, e.g.:

- Exploring a shallow embedding approach
- Leveraging Loom for more foundational pipelines

A back end for **time complexity analysis** is also of interest.

#### Implementing verification paradigms

The formal methods community has a wide range of verification techniques that could be valuable in the Boole ecosystem, e.g.:

- proof by refinement
- techniques for program equivalence
- other deductive verification paradigms

#### Lean automation

Since Boole back ends reduce correctness questions to Lean conjectures, automation is central.

We already rely on key techniques such as `grind` and `lean-smt`. Additional work on automation for conjectures generated from Boole is welcome, including domain-specific automation that remains performant and readable.
