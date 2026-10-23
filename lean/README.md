# Lean formalization of the thrackle bounds

This directory is a Lean 4 project (toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `v4.35.0-rc3`; see
`lean-toolchain` and `lake-manifest.json`). It proves that a thrackleable graph on `n ≥ 4` vertices has at most
`27/20 (n − 1)`, `15/11 (n − 1)`, `51/38 (n − 1)` and `4/3 (n − 1)` edges, from facts about thrackles (`ThrackleAxioms`,
plus `NoSpikeFaces` for the last two bounds) and the computational facts listed below.

## The theorems

| theorem | file | hypotheses | conclusion |
|---|---|---|---|
| `Thrackle78.thrackle_bound` | `Thrackle78/Main.lean` | `ThrackleAxioms`, `CompFacts` | `20 m ≤ 27 (n − 1)` |
| `Thrackle78.thrackle_bound_15_11` | `Thrackle78/Main.lean` | `ThrackleAxioms`, `CompFacts15` | `11 m ≤ 15 (n − 1)` |
| `Thrackle78.thrackle_bound_51_38` | `Thrackle78/Main.lean` | `ThrackleAxioms`, `NoSpikeFaces`, `CompFacts` | `38 m ≤ 51 (n − 1)` |
| `Thrackle78.thrackle_bound_4_3` | `Thrackle78/Main.lean` | `ThrackleAxioms`, `NoSpikeFaces`, `CompFacts`, `ThetaFacts` | `3 m ≤ 4 (n − 1)` |
| `Thrackle78.thrackle_bound_full` | `Thrackle78Full.lean` | `ThrackleAxioms` | `20 m ≤ 27 (n − 1)` |
| `Thrackle78.thrackle_bound_15_11_full` | `Thrackle78Full.lean` | `ThrackleAxioms` | `11 m ≤ 15 (n − 1)` |
| `Thrackle78.thrackle_bound_51_38_full` | `Thrackle78Full.lean` | `ThrackleAxioms`, `NoSpikeFaces` | `38 m ≤ 51 (n − 1)` |
| `Thrackle78.thrackle_bound_4_3_full` | `Thrackle78Full43.lean` | `ThrackleAxioms`, `NoSpikeFaces` | `3 m ≤ 4 (n − 1)` |

Here `m = Nat.card G.edgeSet`, `n = Fintype.card V`, for every graph `G` with `Thr G` and `n ≥ 4`.

- The first four theorems depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`. Their own
  enumerations (the 6-8 and 6-6 overlap lemmas and the two run lemmas on 10-faces) are checked by the kernel
  (`decide +kernel`).
- The `_full` theorems discharge `CompFacts` and `ThetaFacts` with the computational facts in `Thrackle78Facts/`. These
  are proved with `native_decide`, which trusts Lean's compiler, so the `_full` theorems also depend on auxiliary axioms
  named `…._native.native_decide.ax_…`, one for each evaluation. `thrackle_bound_4_3_full` depends on 3,480 of them.

## The hypotheses

`ThrackleAxioms Thr` (`Thrackle78/Hyp.lean`) collects five properties of a thrackleability predicate `Thr`:
- `sub`: a subgraph of a thrackle is a thrackle;
- `c4`: the 4-cycle is not thrackleable;
- `faces`: a 2-connected triangle-free thrackle has the facial structure `FaceData`. This is a list of closed walks
  covering every edge exactly twice, with Euler's inequality, even lengths, simple short faces and the other properties
  listed in `Thrackle78/Defs.lean`;
- `double`: Conway doubling;
- `link`: a thrackle with at least one edge gives, for every oriented edge listing, a crossing system whose augmented
  graph is planar. Planar means no `K₅` and no `K₃,₃` minor.

`NoSpikeFaces Thr` (`Thrackle78/NoSpike.lean`) says that every 2-connected triangle-free thrackle has a `FaceData` whose
walks never turn back along the edge just traversed (`wᵢ ≠ wᵢ₊₂`); it implies `faces`. Only the `51/38` and `4/3`
bounds use it. Section 6 of the paper counts `faces` and `NoSpikeFaces` as one property, so that it lists five.

`CompFacts` and `CompFacts15` (`Thrackle78/Hyp.lean`) and `ThetaFacts` (`Thrackle78/Theta.lean`) state that given
graphs, with their oriented edge listings exactly as computed, are not combinatorially thrackleable:
- the 13 graphs of the 6-8 overlap lemma: `DB(6,8,−1)`, `DB(6,8,−2)`, `DB(6,8,−3)`, `U7` … `U16`;
- the 7 graphs of the 6-6 overlap lemma: `DB(6,6,0)`, `DB(6,6,−1)`, `DB(6,6,−2)`, `DB(6,6,−3)`, `V4`, `V5`, `V7`;
- the 3 graphs of the run lemma for `4/3`: `θ(2,3,3)`, `θ(2,3,4)`, `θ(3,3,7)`, which the paper calls `DB(5,5,−2)`,
  `DB(5,6,−2)` and `DB(6,10,−3)`.

`CompFacts15` omits `DB(6,6,0)` and `V7`.

## The computational facts

The checker accepts "not planar" only with a `K₅` or `K₃,₃` minor that it checks against the graph.
- For 17 of the 20 graphs of `CompFacts`, it verifies certificate trees read from `data/`.
- `DB(6,6,0)`, `DB(6,8,−1)`, `DB(6,8,−2)` and `θ(3,3,7)` are proved by its own sharded search, with filters whose
  soundness is proved. The searches for `DB(6,8,−1)` and `θ(3,3,7)` also use proved symmetry reductions.
- `θ(2,3,3)` and `θ(2,3,4)` are proved by an unfiltered search from the root. They read no data.

## Building

Run `lake` from this directory: the data files are read with paths relative to it.

1. Install the toolchain with `elan`. Optionally fetch Mathlib's prebuilt files with `lake exe cache get`.
2. Download `lean-certificate-data.tar.xz` and `lean-certificate-data-theta337.tar.xz` from the Zenodo record of this
   release (see the README one level up), and unpack both here:
   `tar xJf lean-certificate-data.tar.xz && tar xJf lean-certificate-data-theta337.tar.xz`. This creates `data/`
   (266 files, 11.2 GB).
3. Check the data: `sha256sum -c MANIFEST`. The build also checks every data file against a 64-bit FNV-1a hash written
   next to its path in the `load_cert_chunk` commands of the data modules (`T78Data/`, `T78N*.lean`, `T78T337*.lean`;
   the command is defined in `T78Loader.lean`), and it rejects any byte ≥ 128.
4. Build with lake:
   - `lake build` builds the default target, the library `Thrackle78`: the statements, the four conditional bounds, the
     probes and the soundness proofs of the checker. It needs no data.
   - `lake build Thrackle78Full` builds the 20 facts of `CompFacts` and the `27/20`, `15/11` and `51/38` `_full`
     theorems.
   - `lake build Thrackle78Facts.TH233 Thrackle78Facts.TH234 Thrackle78Facts.TH337` builds the three theta facts.
5. `Thrackle78Full43.lean` proves `thrackle_bound_4_3_full` from these. `lakefile.toml` declares it as a library, but
   the checked build compiled it with `lean` directly:

       LEAN_PATH=<package oleans>:<oleans of step 4>:<out> \
         lean Thrackle78Full43.lean -o <out>/Thrackle78Full43.olean -i <out>/Thrackle78Full43.ilean

   Here `<package oleans>` are the build directories of Mathlib and the other packages (as printed by
   `lake env printenv LEAN_PATH`), `<oleans of step 4>` is one directory tree holding the `.olean` files of step 4, and
   `<out>` is any directory.
6. Print the axioms with the same `LEAN_PATH`: write a file `Ax.lean` with `import Thrackle78Full43` and
   `#print axioms Thrackle78.thrackle_bound_4_3_full`, and run `lean Ax.lean`. The answer is `propext`,
   `Classical.choice`, `Quot.sound` and the 3,480 native-decide axioms.

These steps were not run end to end in one workspace. The facts were built in two workspaces, one for the 20 facts of
`CompFacts` and one for `θ(3,3,7)`, and `Thrackle78Full43` was compiled with `lean` over the merged outputs and checked
there (axioms, `leanchecker --fresh`). The section "Record of the checked build" at the end lists the commands.

### What a build from source re-runs, and its cost

A build from source re-runs every search and every kernel check. Costs are given in process-hours; one process-hour is
one hour of one single-threaded build process. They leave out building Mathlib, whose prebuilt files are fetched in step
1.

| step | work | cost |
|---|---|---|
| library `Thrackle78` (`lake build`) | statements, conditional bounds with the tables of the overlap and run lemmas, soundness proofs of the checker | about 1 process-hour: 107 of its 115 modules took 18 min 50 s on 22 vCPUs with 4 jobs, the other 8 took about 4 process-minutes; each run-lemma slice up to about 12 min, about 7 GB seen per slice |
| 17 certificate facts | data libraries compiled to native code, certificates checked | about 1–3 process-hours (estimated); the largest needs about 15 GB |
| `DB(6,6,0)` | sharded search, 48 batches | about 4 process-hours |
| `DB(6,8,−2)` | sharded search, 96 batches + top + filters | about 180–290 process-hours (3 h 16 min on 90 vCPUs) |
| `DB(6,8,−1)` | symmetry-reduced sharded search, 1,200 batches + top and filter trees | about 480 process-hours, 449 of them for the batches (5 h 45 min on 90 vCPUs) |
| `θ(3,3,7)` | symmetry-reduced sharded search, 1,200 batches + 600 filter-tree shards | about 1,600 process-hours (about 6.5 h on 384 vCPUs) |
| `θ(2,3,3)`, `θ(2,3,4)` | unfiltered search | about 6 s and 1–2 min |

Notes on the figures:
- They were measured in the invocations of the checked build, except those for the library `Thrackle78`, which were
  measured in a later rebuild; the cost of the 17 certificate facts is estimated from the times of single modules.
- The 3 h 16 min given for `DB(6,8,−2)` is the time of one invocation that built `DB(6,8,−2)` and `DB(6,6,0)` together.
- The invocation for `DB(6,8,−1)` shared its machine with smaller invocations that built some of its modules and, for 41
  minutes, with the invocation that built the 17 certificate facts.

The rows sum to about 2,300–2,400 process-hours, on the order of $100 at 2026 cloud spot prices. Each native batch
process uses about 1–2 GB of memory. `LEAN_NUM_THREADS` sets the number of parallel lake jobs; choose it by the memory
available. The checked build used 80 jobs on 90 vCPUs for `DB(6,8,−1)`. For `θ(3,3,7)` it used 220 jobs for the batches
and 50 for the filter-tree shards, on 384 vCPUs. With many jobs, lake needs a large virtual-memory limit (`ulimit -v`).

## Files

- `Thrackle78/`: the statements (`Defs`, `Hyp`, `NoSpike`, `Theta`, `Main`, `Probe`), the proofs (`Proof/`) and the
  Mathlib side of the checker (`Checker/`).
- `Thrackle78Core/`, `T78Data/` and `T78*.lean`: the checker's core (no Mathlib), the data loader, the data modules and
  the inputs of the searches.
- `Thrackle78Facts/`: the computational facts.
- `Thrackle78Full.lean`, `Thrackle78Full43.lean`: the `_full` theorems.
- `gen/`: the generators of the kernel-checked tables (`OverlapData`, `Hex66Data`, `Hex66eData`, `Run610Data`,
  `Run3S*`). They are not needed for building, and they cannot regenerate `data/`.
- `MANIFEST`: the sha256 of every data file, with paths relative to this directory.
- `SHA256SUMS`: the sha256 of every other file in this directory.

The data files are inputs of the checks and need not be trusted. They were produced by programs that are not included:
a C program wrote the certificate trees, and a Lean driver and scripts wrote the split states, filter lists, indices and
hints, partly from files of the paper's runs.

## Record of the checked build

The rest of this file is a record for reviewers: how the checked build was run, a second build, and how this copy
differs from the tree that was built.

The axioms quoted above and the replay by `leanchecker` come from the build recorded here: `lean Ax.lean` printed
`propext`, `Classical.choice`, `Quot.sound` and the 3,480 native-decide axioms, and
`leanchecker --fresh --verbose Thrackle78Full43` replayed `Thrackle78Full43` and all its imports, Mathlib included, and
exited with status 0. The build used two workspaces with the sources of the checked tree (see "This copy" below):
workspace 1 for the 20 facts of `CompFacts` and workspace 2 for `θ(3,3,7)`. A third directory, the overlay directory,
sat on top of workspace 1. The modules of the build outside Mathlib break down as follows:

| modules | number |
|---|---|
| built in workspace 1 | 1,797 |
| added in the overlay directory | 69 |
| built only in workspace 2 | 1,864 |
| `Thrackle78Full43`, compiled with `lean` | 1 |
| total, each replayed by `leanchecker` | 3,731 |
| in the import closure of `Thrackle78Full43`, itself included (all except `Thrackle78.Probe` and `T78Data`, a module that only imports the data modules) | 3,729 |
| built in workspace 2 and also in workspace 1 (48) or the overlay directory (3), with equal declarations (compared constant by constant) | 51 |

### Commands

Settings common to the invocations:
- In workspaces 1 and 2, every invocation ran with `ulimit -v 4000000000`, because with a small limit lake aborts with
  "failed to create thread"; the two invocations in the overlay directory ran without it.
- Each invocation had `LEAN_NUM_THREADS` set to its number of jobs.
- In workspace 2, every invocation ran under `nice -n 19`.
- Most ran in a memory-capped scope (`systemd-run --scope -p MemoryMax=<cap> -p MemorySwapMax=0`); the comments give the
  caps in systemd's notation, where `G` means GiB.

Workspace 1:

    LEAN_NUM_THREADS=100 lake build Thrackle78Facts.DB682 Thrackle78Facts.DB660
    LEAN_NUM_THREADS=80 lake build Thrackle78Facts.DB681                                # MemoryMax=320G
    LEAN_NUM_THREADS=2 lake build Thrackle78Facts.DB661 Thrackle78Facts.DB662 Thrackle78Facts.DB663 \
      Thrackle78Facts.DB683 Thrackle78Facts.U7 ... Thrackle78Facts.U16 \
      Thrackle78Facts.V4 Thrackle78Facts.V5 Thrackle78Facts.V7                          # MemoryMax=60G

Concurrent invocations on the same tree built these modules of `Thrackle78Facts.N681` that `DB681` needs, so that they
would start earlier:
- `Idxh12` and `Idxh54` (10 jobs; this invocation built only these two);
- `Top`, `FT0`–`FT2`, `HToph12` and `Coverh54` (6 jobs, MemoryMax=40G);
- `HS0`–`HS299` (8 jobs, MemoryMax=40G).

The overlay directory held workspace 1's sources unchanged and the new modules. Of the files that only workspace 2
built, it had just `Thrackle78/Checker/FilterXF.lean`, which none of its targets imports. Its `.lake/build` was an
overlay whose read-only lower layer was workspace 1's build directory. The kernel part and the facts for `θ(2,3,3)` and
`θ(2,3,4)` were built there:

    LEAN_NUM_THREADS=8 lake build --no-build <the 20 fact modules>         # all up to date; MemoryMax=250G
    LEAN_NUM_THREADS=32 lake build Thrackle78.Main Thrackle78.Probe Thrackle78.Checker.SymT337Q \
      Thrackle78Facts.TH233 Thrackle78Facts.TH234 Thrackle78Full                        # MemoryMax=250G

Of the 69 modules that these targets add, 27 were built by the second invocation and 42 had been built earlier in the
same directory.

Workspace 2, where the core libraries and the checker had already been built from the same sources:

    LEAN_NUM_THREADS=16 lake build T78T337D T78T337 T78T337T T78T337H Thrackle78.Checker.FilterXF \
      Thrackle78.Checker.SymT337Q Thrackle78.Checker.FilterAut
    LEAN_NUM_THREADS=5 lake build Thrackle78Facts.T337.Top Thrackle78Facts.T337.Idxc10a Thrackle78Facts.T337.Idxc10b \
      Thrackle78Facts.T337.HTopc10a Thrackle78Facts.T337.Coverc10b                      # MemoryMax=70G
    LEAN_NUM_THREADS=1 lake build Thrackle78Facts.T337.HTopc10a                         # MemoryMax=30G
    LEAN_NUM_THREADS=50 lake build Thrackle78Facts.T337.HS0 ... Thrackle78Facts.T337.HS599     # MemoryMax=140G
    LEAN_NUM_THREADS=220 lake build Thrackle78Facts.T337.B0 ... Thrackle78Facts.T337.B1199     # MemoryMax=420G
    LEAN_NUM_THREADS=20 lake build Thrackle78Facts.T337.Soundc10b                       # MemoryMax=60G
    LEAN_NUM_THREADS=32 lake build Thrackle78Facts.TH337                                # MemoryMax=100G

The generated files shipped here contain `import Thrackle78.Theta`, and `Idxc10a` and `Idxc10b` were built twice. The
first launch of the invocation for `Top`, `Idxc10a`, `Idxc10b`, `HTopc10a` and `Coverc10b`, and of those for the shards
and the batches, used generated files that lacked the import: `Top`, `Coverc10b`, `Idxc10a` and `Idxc10b` built, while
the modules that mention the listing `lTH337` (`HTopc10a` and every batch and shard module) stopped with elaboration
errors within seconds. After the files were regenerated with the import, the shard and batch invocations were started
again, the single-job invocation built `HTopc10a`, and the invocation for `Thrackle78Facts.TH337` rebuilt `Idxc10a` and
`Idxc10b`, whose regenerated files differ by the added import.

`Thrackle78Full43` was compiled over one tree that holds the `.olean` files of the overlay directory and those only in
workspace 2. Lean resolves a module in the first `LEAN_PATH` entry that contains its root directory (`Thrackle78`,
`Thrackle78Facts`), so the two sets must share one tree:

    mkdir -p MERGED/lib/lean OUT/lib/lean
    cp -as <overlay directory>/.lake/build/lib/lean/. MERGED/lib/lean/
    cp -as <the .olean files only in workspace 2>/. MERGED/lib/lean/
    export LEAN_PATH=<package directories>:MERGED/lib/lean:OUT/lib/lean
    lean Thrackle78Full43.lean -o OUT/lib/lean/Thrackle78Full43.olean -i OUT/lib/lean/Thrackle78Full43.ilean

Here `<package directories>` are the entries of `lake env printenv LEAN_PATH` other than the workspace's own build
directory. With the same `LEAN_PATH`, `lean Ax.lean` printed the axioms.

For the replay, the toolchain's `bin` directory came first on `PATH`, and the runs used real copies of the files, since
`leanchecker` does not find modules through symbolic links.
- Per-module runs: each of the 3,731 modules was replayed separately, 40 at a time; this took 15 minutes with
  `MemoryMax=300G`.
- `leanchecker --fresh --verbose Thrackle78Full43` took 1 h 23 min on one thread, without a cap, on another machine. It
  ran over copies of the files that had been checked against their sha256. Apart from the line "replaying
  Thrackle78Full43 with --fresh" that `--verbose` prints, it produced no output.
- The compile, the axioms and the comparison of the shared modules: `MemoryMax=250G`.

### A second build

A second build was made separately, on other machines, from the sources of the checked build. It ran every search behind
the 3,480 native-decide axioms again. The 1,797 `.olean` files of workspace 1 and the 1,864 that only workspace 2 has
came out byte-identical to those of the checked build. Nine checker files that workspace 2 shares with workspace 1
(eight) or the overlay directory (one) differed only in the source path stored in them; their declarations are
identical. For `θ(3,3,7)`, a single invocation of `lake build Thrackle78Facts.TH337` with 340 jobs built the 1,915
modules of that fact in 10 h 10 min, without errors and without `sorry`. Run once per module, `leanchecker` accepted
each of the 1,867 modules of this part. `Thrackle78Full43`, compiled with `lean` over the outputs of the second build,
has the same axioms as in the checked build. For `thrackle_bound_4_3_full` these are the three standard axioms and the
3,480 native-decide axioms, each of which is the evaluation of one checker run; for `thrackle_bound_4_3` they are the
three standard axioms alone. `leanchecker --fresh Thrackle78Full43` also replayed this environment, Mathlib included,
and exited with status 0; it took the native-decide axioms as given. A filter-tree shard with its claim negated failed,
and data files with one byte changed were rejected by their pinned hashes.

### This copy

The checked build was made from a tree that differs from this copy in three ways:
- internal labels were removed from the comments and docstrings of eight Lean files and of `lakefile.toml`;
- an unused first draft of the statements (three files under `Thrackle/` that no other file imports) was deleted,
  with its library entry in `lakefile.toml`;
- the default target in `lakefile.toml` was set to `Thrackle78`.

We compared the two trees file by file. All other files present in both are byte-identical, the eight Lean files are
identical once comments and docstrings are removed, and `lakefile.toml` differs only as described. The 107 modules that
use no `native_decide` (`Thrackle78.Main`, `Thrackle78.Probe`, `Thrackle78.Checker.SymT337Q` and their imports) were
rebuilt from these sources. Compared as Lean expressions, their 3,598 constants are the same as in the checked build,
and so are the axioms for the four conditional bounds, the two no-spike probes and the four lemmas behind the symmetry
reductions. The compiled files of a build of this copy are not byte-identical to those of the checked build, since
docstrings are stored in them.
