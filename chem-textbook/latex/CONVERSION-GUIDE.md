# Markdown-to-LaTeX Conversion Guide

This guide documents how each structural element in the chemistry textbook's markdown files maps to the LaTeX environments defined in `chem-preamble.sty`.

## Quick Reference

| Markdown Element | LaTeX Environment/Command |
|-----------------|--------------------------|
| `# Chapter Title` | `\chapter{Title}` (in main .tex file) |
| `## COM.1: Section Title` | `\section{COM.1: Section Title}` |
| `### Subsection` | `\subsection*{Subsection}` |
| Reasoning move blockquote | `\begin{reasoningmove}{ID}{Name}` |
| `*Depends on: ...*` | `\depends{ID}{description}{chapter}` |
| Reasoning Chain callout | `\begin{reasoningchain}{Title}` + `\chainitem{}{}{}` |
| Practice Questions section | `\begin{practicequestions}` + `\practiceq{}` |
| Enrichment section | `\begin{enrichment}{Title}` |
| CP capstone section | `\begin{cpcapstone}{ID}{Title}` + `\cpstep{}{}` |
| Chapter Summary table | `\begin{chaptersummary}` + tabular |
| Chemical formula (inline) | `\ce{H2O}`, `\ce{Na+}`, `\ce{CO2}` |
| Chemical reaction (display) | `\reaction{2 H2 + O2 -> 2 H2O}` |
| Temperature | `\SI{100}{\degreeCelsius}` |
| Concentration | `\SI{0.1}{\molar}` |
| Figure placeholder | `\figurebox{Description}{fig:label}` |
| Real-world hook box | `\begin{hook}{Title}` |
| Bold taxonomy ID | `\textbf{PRIM-COM001}` |
| Equilibrium arrow | `\ce{<=>}` (in mhchem) |

## Conversion Procedure

### For each chapter file:

1. **Remove the `# Chapter` header** — the `\chapter{}` command is in `chem-textbook.tex`
2. **Convert sections**: `## COM.1: Title` → `\section{COM.1: Title}\label{sec:com1}`
3. **Convert subsections**: `### Title` → `\subsection*{Title}` (unnumbered)
4. **Convert reasoning moves**: The blockquote pattern:
   ```markdown
   ### **PRIM-COM001: Atomic Composition Analysis**
   > **Reasoning move**: Given a substance...
   ```
   becomes:
   ```latex
   \begin{reasoningmove}{PRIM-COM001}{Atomic Composition Analysis}
     \textbf{Reasoning move}: Given a substance...
   \end{reasoningmove}
   ```

5. **Convert dependency annotations**:
   ```markdown
   *Depends on: PRIM-COM001 (you need to know what Z means...)*
   ```
   becomes:
   ```latex
   \depends{PRIM-COM001}{you need to know what $Z$ means...}{1}
   ```

6. **Convert Reasoning Chains**:
   ```markdown
   > **Reasoning Chain: Why does salt dissolve?**
   > 1. *PRIM-COM004 (Substance classification)*: NaCl is ionic...
   > 2. *PRIM-STR001 (Bond type)*: Na+ and Cl- are held by...
   ```
   becomes:
   ```latex
   \begin{reasoningchain}{Why does salt dissolve?}
     \chainitem{PRIM-COM004}{Substance classification}{NaCl is ionic...}
     \chainitem{PRIM-STR001}{Bond type}{\ce{Na+} and \ce{Cl-} are held by...}
   \end{reasoningchain}
   ```

7. **Convert practice questions**:
   ```markdown
   1. A water quality report lists arsenic...
   2. Two atoms are found in a sample...
   ```
   becomes:
   ```latex
   \begin{practicequestions}
     \practiceq{A water quality report lists arsenic...}
     \practiceq{Two atoms are found in a sample...}
   \end{practicequestions}
   ```

8. **Convert chemical formulas**: All inline formulas use `\ce{}`:
   - `H₂O` → `\ce{H2O}`
   - `Na⁺` → `\ce{Na+}`
   - `CO₂` → `\ce{CO2}`
   - `N₂ + 3H₂ ⇌ 2NH₃` → `\ce{N2 + 3 H2 <=> 2 NH3}`

9. **Convert tables**: Markdown tables → `tabular` with `booktabs`:
   ```latex
   \begin{tabular}{lll}
     \toprule
     \textbf{Col 1} & \textbf{Col 2} & \textbf{Col 3} \\
     \midrule
     data & data & data \\
     \bottomrule
   \end{tabular}
   ```

10. **Convert enrichment sections**: Wrap with `\begin{enrichment}{Title}`

11. **Convert CP capstones**: Use `\begin{cpcapstone}{CP-NNN}{Title}` with `\cpstep{Step Name}{Content}`

## File Naming Convention

| Markdown File | LaTeX File |
|--------------|-----------|
| `FRONT-MATTER.md` | `ch-preface.tex`, `ch-toolkit.tex`, `ch-notation.tex`, `ch-howtoread.tex` |
| `CH-01-COM.md` | `ch-01-com.tex` |
| `CH-02-STR.md` | `ch-02-str.tex` |
| `CH-03-NRG.md` | `ch-03-nrg.tex` |
| `CH-04-SCL.md` | `ch-04-scl.tex` |
| `CH-05-CHG.md` | `ch-05-chg.tex` |
| `CH-06-MULTI.md` | `ch-06-multi.tex` |
| `BACK-MATTER.md` | `ch-glossary.tex`, `ch-hookindex.tex`, `ch-answers.tex` |

## Build

```bash
cd chem-textbook/latex/
make
# or: latexmk -pdf chem-textbook.tex
```

Requires: TeX Live 2023+ with packages: memoir, mhchem, siunitx, tcolorbox, booktabs, tikz, hyperref, cleveref.
