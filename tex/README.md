# Paper draft (IEEE CSF)

`main.tex` is the paper; each section is a file in `sections/`, and
`references.bib` the bibliography. Build with `latexmk -pdf main.tex`, from a copy
off OneDrive.

## Links to the mechanisation

Write a Rocq name as `\m{name}`, for example `\m{restore_invariant_noop}`. It is
typeset like `\code{name}` and links to the line of `theories/*.v` that defines it.
`\mechfile{theories/models.v}{models.v}` links a whole file, and `\url{\repobase}`
is the repository root.

Line numbers are never written by hand. `mechlinks.py` scans `../theories/*.v` for
every `Lemma`, `Theorem`, `Definition` and so on, and writes the table
`mechlinks.tex` (name, file, line). `.latexmkrc` runs it before every `latexmk`
build, so the links follow the development as it changes. A name that is not in the
table is typeset without a link and reported as a LaTeX warning
(`No definition found for ...`); a name defined in two files links to the first and
is reported by the script.

The line numbers are those of the local files. They match GitHub only once those
files are pushed, so push before sharing a PDF.

Where the links point is decided in one place, near the top of `main.tex`:

| switch | links point to | use for |
|---|---|---|
| `\anonymoustrue` | the Anonymous GitHub mirror, `https://anonymous.4open.science/r/<id>/<path>#L<line>` | submission |
| `\anonymousfalse` | `https://github.com/Tirore96/NonInterference/blob/main/<path>#L<line>` | camera-ready |

Check that the mirror honours `#L<line>` once it exists; if it does not, the links
still reach the right file.

## Workflow

1. Work in this repository as usual. Commit and push to `main` when a change should
   become visible to reviewers.
2. The Anonymous GitHub mirror (anonymous.4open.science) is created once, from the
   GitHub account, for `Tirore96/NonInterference`, branch `main`, with
   auto-update enabled. It then follows `main`, so pushed changes reach the mirror
   without recreating it, and the id in its URL stays the same.
3. Put that id into `\repobase` in `main.tex` (the `XXXX` placeholder).
4. Before submitting, open the mirror and check that nothing identifying shows.

### What to anonymise

Give Anonymous GitHub these terms to redact: `Tirore96`, `Tirore`, `Dawit`,
`Willard`, `wilr`, `itu.dk`, `IT University`.

Two things it cannot fix by redacting terms:

- **This folder.** `tex/` names the authors, so it should not be in the mirrored
  branch while the paper is under review. Keep it out of `main` (for instance in a
  private repository or on a separate branch that is not mirrored).
- **`notes/willard_gist.txt`.** The file name identifies a person. Rename or remove
  it before the mirror is created.

The development cites Rafnsson et al. (POST 2017) as prior work. Redacting
`Rafnsson` would garble those citations, so it is left out of the list; citing one's
own earlier work in the third person is normal under double-blind review.
