# Clebsch and Schläfli figure embeddings

The five Clebsch panels and fourteen Schläfli panels match the finite model lists
in `EPPAIII/Primitive/ClebschSchlafliModels.lean`. Each match identifies the
ambient host and the actual selected vertex set. Each representative occurs
once.

The audit uses the panel filenames and order in frozen R17, whose TeX SHA-256 is
`2caf4ce1d4f158dda5f6e98859223a3e9fadef591334988f61f1194dde5f7c71`. The
panel hashes in the table identify the available source artwork that was
verified. A TeX include records a filename. The PDF hashes identify its audited
contents.

## Reproduction

Run from the repository root.

```sh
python3 checks/primitive_figure_audit.py checks/primitive_figure_panels.json
```

The standard-library check verifies that every recorded ambient graph is
isomorphic to the appropriate model, each second permutation is a host
automorphism, and the composed map takes the selected subset to its stated Lean
representative. It checks that each Lean mask occurs once.

To verify the extraction against the original vector graphics, put the panels
`clebsch-1.pdf` through `clebsch-5.pdf` and `schlafli-1.pdf` through
`schlafli-14.pdf` under a single directory. The SHA-256 column below
disambiguates versions with similar filenames. Install PyMuPDF and run

```sh
python3 checks/primitive_figure_audit.py checks/primitive_figure_panels.json \
  --pdf-dir /path/to/Pictures --manuscript /path/to/frozen-R17.tex
```

Add `--write` with a separate output pathname to regenerate the manifest
from the PDFs. The parser identifies vertices from the cubic marker paths and
edges from the single-segment paths. Black markers define the selected vertex
set. In each Schläfli panel, the central dot and two overlapping circles are
separate vertices. An edge endpoint at the center belongs to the dot. A
clipped endpoint belongs to the circle at its radius. Every endpoint had a
unique match within 0.01 PDF points. The maximum residual over the tested
Schläfli endpoints was below 0.006 points, and the distance residual for the
next candidate was above 2.24 points. The audit checks that an edge is black
exactly when both its endpoint markers are black.

This establishes the correspondence between the drawings and the labeled
model masks. The older independent finite obstacle enumeration establishes
the search results externally. Lean takes the two `CanonicalFigureClassification` results as computational
premises. The correspondence check is independent of the solver audit.

## Panel correspondence

| Panel | Size | Relabelled mask | Lean representative | SHA-256 |
|---|---:|---:|---:|---|
| clebsch-1.pdf | 8 | 30840 | 831 | bacc2b79720f7799d7d52fef8fbec7ef2b59062c61de5276d355e2eebfee82f1 |
| clebsch-2.pdf | 8 | 62400 | 975 | dbccbb575fcd03183cc3286fd02b9cafd3a41eee3d342f334903f7486ec83195 |
| clebsch-3.pdf | 8 | 65280 | 255 | 7329421420db0d97f1b73fa94b50e2922f938160c13989c586bed2895370fc0e |
| clebsch-4.pdf | 9 | 56272 | 1911 | 7abb598ec3d746a769b4299ae0090f7c35848e2ae5d25e4f2aeb452391b930df |
| clebsch-5.pdf | 10 | 48596 | 6014 | b51ae38bfb4b38ce739c1334c3fdabcc60e63ff9119fac9eebae7c4b496b49dd |
| schlafli-1.pdf | 14 | 123785048 | 63455 | d3138507e1c247709f498dbdf78a617b7239103e1c820188725ae39a3ede1457 |
| schlafli-2.pdf | 14 | 130528328 | 440295 | 07e42a274d7b27201005af1739a5ee526722119c0153380be00c6745bf59dc43 |
| schlafli-3.pdf | 14 | 115595824 | 517997 | 147f757ebaaa77da43092af9830758fb4b3ddc2f82db93b4384052e0a7d2ec2f |
| schlafli-4.pdf | 14 | 125055578 | 452589 | f538c4966ddfa2740985aedf44ac248707b0199f894bd831958acc606fe02706 |
| schlafli-5.pdf | 14 | 82691416 | 419823 | 6c9a46932484474d3d59667e0c495b4bce748d503b8b395e812fa4bd81590cc8 |
| schlafli-6.pdf | 14 | 132371496 | 3072988 | d3c1f34cc1df4b9987cda8e84d3612813d12ac67f4046fa61718f322cd5cb8d0 |
| schlafli-7.pdf | 14 | 116711532 | 2803687 | 5ff43f7f0c012fe80de03649c202ff49f8ac317554561cf0f34fab6095f1dded |
| schlafli-8.pdf | 15 | 132006010 | 1042300 | 69839b397b23ad597170c057b2d5de0c86f4ed20a91a39c449b1978442efd2ac |
| schlafli-9.pdf | 15 | 132014194 | 976892 | ba7354271d8b370e3b1788bce962a338fd27f0f6f54bf8d3710af9950d1a24e3 |
| schlafli-10.pdf | 15 | 134213632 | 16630264 | 003600b0d5761818bf0aed446c60fe815e9429cabb4af7984e59fdf0d804d22d |
| schlafli-11.pdf | 15 | 125031528 | 7164891 | 158701037ddd17ecc3b3efe0147579c25425574dcb2310b11208f6fb3df2b7ca |
| schlafli-12.pdf | 15 | 66310504 | 2803679 | 2a0cb838af44600d66ad1eec64053dcfd4b175456bbb12838c5f29258fc6a42e |
| schlafli-13.pdf | 16 | 132247362 | 2092860 | 295a08ea44bfd13b70ba39b885f5ba07e1ea5009701b2daa4e6384a6cf4377e3 |
| schlafli-14.pdf | 16 | 125284946 | 976863 | 99cf87bc0c91f198176457c51d80f58f331da49b5ef8f9795f845f7ccee8c75a |
