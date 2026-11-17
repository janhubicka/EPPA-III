# Publishing the EPPA III Lean wiki

This documentation is version-controlled in `docs/wiki/`, as in `lean-milliken`, `lean-successors`, `lean-all-those-ramsey-classes`, and `lean-ramsey-space-todorcevic`. The [publishing workflow](../../.github/workflows/publish-wiki.yml) uses `Andrew-Chen-Wang/github-wiki-action@v5` with preprocessing, Git cloning, and no empty commits.

## GitHub Actions

On a push touching `docs/wiki/**` or the workflow, or on manual dispatch, the workflow:

1. Checks out the requested source revision.
2. Authenticates Git with `GITHUB_TOKEN` (using `gh auth setup-git`).
3. Checks whether the independent `EPPA-III.wiki.git` repository has been initialized.
4. If present, synchronizes the source-controlled Markdown to the [live Wiki tab](https://github.com/janhubicka/EPPA-III/wiki). The third-party publishing action currently invokes `git push -f origin master`; it avoids empty commits but **does force-push**. Direct edits to the live Wiki may therefore be overwritten.
5. If missing, writes an explicit notice to the Action's step summary. **The wiki is not published in that case.**

**Published (17 November 2026):** The source-controlled documentation was merged in [PR #401](https://github.com/janhubicka/EPPA-III/pull/401). The first Wiki Home page initialized `EPPA-III.wiki.git`, automatically triggering [publishing run #44068392794](https://github.com/janhubicka/EPPA-III/actions/runs/44068392794). The run checked 47 exact Lean snippets and pushed Wiki commit `383f15d` to `master`, publishing `Home.md`, `Imprimitive-Classification.md`, `Gardiner-External-Assumption.md`, `Named-Host-Models.md`, `Primitive-classification.md`, `Primitive-classification-assumptions.md`, `Publishing.md`, and `_Sidebar.md`. A green run with a **skipped** publishing step would not establish publication; this one completed the actual push. Wiki publication does not itself verify Lean proofs.

## One-time Wiki initialization if required

GitHub stores Wiki pages in a distinct Git repository. Enabling the Wiki feature (`has_wiki: true`) does **not** establish that the Wiki Git repository already has a first commit.

If the workflow reports an uninitialized Wiki, open [EPPA III Wiki](https://github.com/janhubicka/EPPA-III/wiki), choose **Create the first page**, name it **Home**, add a temporary sentence, and save. Then use [Actions → Publish EPPA III wiki](https://github.com/janhubicka/EPPA-III/actions/workflows/publish-wiki.yml) to run the publisher (or make another change to `docs/wiki/`). The publishing workflow is now on the default branch, so manual `workflow_dispatch` can be used when needed. This is the same one-time procedure documented and successfully used in `lean-milliken`.

## Source of truth and links

- `docs/wiki/README.md` is the front page (published as Wiki Home by preprocessing).
- `docs/wiki/_Sidebar.md` supplies the navigation.
- Relative links to `../../EPPAIII/...` are processed to repository source links.
- Versioned pages must always describe the **actual** Lean theorem, its external hypotheses, and its proof-status boundaries.
- Manual Wiki edits can be overwritten by the next GitHub Actions sync. Make substantive edits in `docs/wiki/` through a PR instead.

## Audit evidence

The repository's regular Lean job builds the formalization and runs `CheckAxioms.lean`, which checks the exposed theorem interfaces for unexpected axioms and rejects `sorry` and custom `axiom` placeholders. A passing wiki-publishing job only proves successful publication, **not** kernel verification. Consult the Lean build run on the same commit for that.
