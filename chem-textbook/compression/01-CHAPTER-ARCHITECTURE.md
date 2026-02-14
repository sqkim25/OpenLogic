# Phase 3: Chapter Architecture

**Date:** 2026-02-14
**Depends on:** 00-STRATEGIC-DECISIONS.md (all 5 decisions), taxonomy/DOMAIN-*.md (dependency graphs)
**Purpose:** Complete chapter/section skeleton for Phase 4 writers. Every taxonomy item is placed in exactly one section. CP deployment verified. Cross-references cataloged.

---

## Overview

| Ch | Working Title | Domain | Sections | Items | CP Capstones | Est. Pages |
|----|--------------|--------|----------|-------|-------------|------------|
| 1 | What Is Stuff Made Of? | COM | 6 (5C + 1E) | 13 | — | 35 |
| 2 | How Does Arrangement Determine Properties? | STR | 6 (5C + 1E) | 15 | — | 39 |
| 3 | What Drives Change? | NRG | 5 (4C + 1E) | 11 | — | 32 |
| 4 | How Much? How Big? | SCL | 7 (4C + 1E + 2CP) | 11 | CP-001, CP-004 | 43 |
| 5 | What Happens? | CHG | 10 (5C + 1E + 4CP) | 12 | CP-002, CP-003, CP-005, CP-006 | 58 |
| 6 | Chemistry Meets Life | MULTI | 1 | — | CP-007 | 10 |
| — | Front matter | — | — | — | — | 6 |
| — | Back matter | — | — | — | — | 6 |
| | **Totals** | | **35 sections** | **62 items** | **7 CPs** | **~229** |

---

## Chapter 1: What Is Stuff Made Of? (COM)

**Governing question**: What are substances made of, and how do we identify and count their building blocks?

### COM.1: What are atoms, and how do we identify them?
- **Items introduced**: PRIM-COM001 (atomic composition analysis), PRIM-COM002 (elemental identity)
- **Depends on**: none (opening section)
- **Cross-chapter refs**: none (COM is the root domain)
- **Est. pages**: 7
- **Key content**: Introduces atoms as the smallest units retaining elemental identity, composed of protons, neutrons, and electrons. Establishes the periodic table as a lookup tool indexed by atomic number Z, linking proton count to element name and symbol.

### COM.2: What can the periodic table predict?
- **Items introduced**: PRIM-COM003 (periodic position reasoning), DEF-COM005 (electronegativity), PRIM-COM007 (valence electron reasoning)
- **Depends on**: COM.1
- **Cross-chapter refs**: none
- **Est. pages**: 8
- **Key content**: Extracts qualitative predictions from periodic table position — atomic size, electronegativity, and reactivity trends. Defines electronegativity as the periodic trend governing electron attraction in bonds. Connects group number to valence electron count and uses the octet rule to predict bonding behavior.

### COM.3: How do we read and classify chemical substances?
- **Items introduced**: PRIM-COM004 (substance classification), PRIM-COM005 (chemical formula reading), PRIM-COM006 (conservation of atoms)
- **Depends on**: COM.1, COM.2
- **Cross-chapter refs**: none
- **Est. pages**: 7
- **Key content**: Classifies matter as element, compound, or mixture. Introduces chemical formula notation. Establishes conservation of atoms: atoms rearrange in chemical processes but are neither created nor destroyed — the foundation for equation balancing (CHG) and stoichiometric reasoning (SCL).

### COM.4: What are isotopes and ions?
- **Items introduced**: DEF-COM001 (isotope), DEF-COM002 (ion)
- **Depends on**: COM.1, COM.2
- **Cross-chapter refs**: none
- **Est. pages**: 6
- **Key content**: Isotopes as atoms of the same element with different neutron counts (same chemistry, different mass and nuclear stability). Ions as atoms/groups with net charge from gaining or losing electrons, with charge predictable from periodic position. Completes the identity toolkit.

### COM.5: How do we think in causal chains?
- **Items introduced**: PRIM-COM008 (causal chain reasoning — scaffolded)
- **Depends on**: COM.1–COM.4 (needs chemical examples to practice with)
- **Cross-chapter refs**: none
- **Est. pages**: 3
- **Key content**: Brief scaffolding section naming the transferable meta-reasoning skill: "Given an observation, identify relevant primitives, connect them causally, arrive at a conclusion." Students practice distinguishing complete from incomplete causal chains. This skill is deployed in every subsequent chapter (see Decision 3).

### COM.E: How do formulas connect to mass measurements? (E)
- **Items introduced**: DEF-COM003 (molecular vs. empirical formula) (E), DEF-COM004 (percent composition) (E)
- **Depends on**: COM.3
- **Cross-chapter refs**: none
- **Est. pages**: 4
- **Key content**: Enrichment — distinguishes molecular from empirical formulas and calculates percent composition by mass. Valuable quantitative skill but not required by any downstream Core item. Absent from CLUE and CIC reformed curricula.

---

## Chapter 2: How Does Arrangement Determine Properties? (STR)

**Governing question**: How do the spatial arrangement and bonding of atoms determine a substance's chemical behavior and physical properties?

### STR.1: How do atoms connect?
- **Items introduced**: DEF-STR001 (Lewis structure), PRIM-STR001 (bond type classification)
- **Depends on**: none within STR
- **Cross-chapter refs**: PRIM-COM007 (valence electrons, COM.2) ← backward; DEF-COM005 (electronegativity, COM.2) ← backward
- **Est. pages**: 7
- **Key content**: Translates valence electron counts into Lewis structures showing bonding pairs, lone pairs, and multiple bonds. Classifies bonds as nonpolar covalent, polar covalent, or ionic using electronegativity difference. Entry point to all structural reasoning.

### STR.2: Where do the electrons sit, and what shape does the molecule take?
- **Items introduced**: PRIM-STR002 (bond polarity reasoning), PRIM-STR003 (molecular shape reasoning), DEF-STR002 (molecular polarity)
- **Depends on**: STR.1
- **Cross-chapter refs**: DEF-COM005 (electronegativity, COM.2) ← backward
- **Est. pages**: 8
- **Key content**: Locates partial charges using electronegativity difference. Applies VSEPR to predict 3D geometry. Combines bond dipoles with geometry to determine net molecular polarity. Contains the core geometric reasoning of the STR domain.

### STR.3: What holds molecules near each other?
- **Items introduced**: DEF-STR003 (hydrogen bond), PRIM-STR004 (intermolecular force hierarchy), DEF-STR006 (phase from IMF balance)
- **Depends on**: STR.2
- **Cross-chapter refs**: none (all dependencies intra-chapter)
- **Est. pages**: 7
- **Key content**: Defines hydrogen bonding. Ranks all IMFs: London dispersion < dipole-dipole < hydrogen bonding < ionic. Connects IMF strength to phase (solid/liquid/gas). Bridges intramolecular bonds (STR.1) and intermolecular forces — a persistent source of student confusion.

### STR.4: How does structure predict what a substance does?
- **Items introduced**: PRIM-STR005 (structure-to-property inference), DEF-STR004 ("like dissolves like"), DEF-STR010 (water as solvent)
- **Depends on**: STR.2, STR.3
- **Cross-chapter refs**: none (intra-chapter)
- **Est. pages**: 7
- **Key content**: Completes the structure-to-property chain: given polarity and IMF type, predict boiling point, viscosity, and solubility direction. "Like dissolves like" as the governing solubility heuristic. Water as an exceptional solvent due to bent geometry, high polarity, and hydrogen-bonding capacity.

### STR.5: Why does carbon build so many molecules?
- **Items introduced**: DEF-STR005 (isomer recognition), DEF-STR007 (carbon backbone reasoning), DEF-STR008 (polymer reasoning)
- **Depends on**: STR.1, STR.2, STR.3
- **Cross-chapter refs**: PRIM-COM007 (valence electrons, COM.2) ← backward
- **Est. pages**: 7
- **Key content**: Isomers prove that composition alone does not determine properties. Carbon's 4-bond versatility enables chains, branches, and rings. Polymers: how monomer identity, chain length, branching, and IMFs determine material properties.

### STR.E: How do metals hold together? (E)
- **Items introduced**: DEF-STR009 (metallic structure) (E)
- **Depends on**: STR.1
- **Cross-chapter refs**: DEF-COM002 (ion, COM.4) ← backward
- **Est. pages**: 3
- **Key content**: Enrichment — electron sea model of metallic bonding. Explains conductivity, malleability, ductility from non-directional bonding. Not required by any downstream Core item.

---

## Chapter 3: What Drives Change? (NRG)

**Governing question**: What determines whether energy flows into or out of a chemical system, and what makes a process favorable?

### NRG.1: Where does energy go?
- **Items introduced**: PRIM-NRG001 (energy tracking), DEF-NRG001 (heat vs. temperature), DEF-NRG005 (calorie/joule)
- **Depends on**: none (chapter opener)
- **Cross-chapter refs**: PRIM-COM006 (conservation of atoms, COM.3) ← backward (analogous conservation principle)
- **Est. pages**: 8
- **Key content**: Energy conservation as the foundational accounting principle. Heat (energy transfer) vs. temperature (average kinetic energy) — correcting the most pervasive non-majors conflation. Joules and Calories connected via nutrition labels.

### NRG.2: Why do some reactions release energy?
- **Items introduced**: PRIM-NRG002 (bond energy reasoning), PRIM-NRG003 (exo/endothermic classification), DEF-NRG003 (enthalpy change, ΔH)
- **Depends on**: NRG.1
- **Cross-chapter refs**: none
- **Est. pages**: 8
- **Key content**: Corrects "breaking bonds releases energy" misconception. Introduces exo/endo binary via energy diagrams. Qualitative ΔH sign convention (no Hess's law). This is the anchor REWRITE section (see Decision 2).

### NRG.3: What makes a process probable?
- **Items introduced**: PRIM-NRG004 (entropy reasoning), PRIM-NRG005 (spontaneity reasoning)
- **Depends on**: NRG.2
- **Cross-chapter refs**: none
- **Est. pages**: 7
- **Key content**: Entropy as probability of arrangements (not "disorder"). Four-case spontaneity matrix. Temperature as the referee between energy and entropy. Qualitative only — no ΔG equation.

### NRG.4: What stops a favorable reaction from happening?
- **Items introduced**: PRIM-NRG006 (activation energy reasoning), DEF-NRG002 (specific heat capacity)
- **Depends on**: NRG.1, NRG.2
- **Cross-chapter refs**: none
- **Est. pages**: 6
- **Key content**: Activation energy barrier resolves the "favorable but not happening" paradox. Energy diagrams with Ea hump. Specific heat as different substances' responses to the same energy input.

### NRG.E: Can free energy settle the tie? (E)
- **Items introduced**: DEF-NRG004 (free energy, conceptual) (E)
- **Depends on**: NRG.3
- **Cross-chapter refs**: none
- **Est. pages**: 3
- **Key content**: Enrichment — conceptual free energy as the single bookkeeping quantity combining enthalpy and entropy favorability. No ΔG = ΔH - TΔS equation. PRIM-NRG005 (Core) already provides the reasoning; this formalizes it.

---

## Chapter 4: How Much? How Big? (SCL)

**Governing question**: How do we bridge the gap between individual molecules and the macroscopic world we measure and observe?

### SCL.1: How do molecules become measurable?
- **Items introduced**: PRIM-SCL001 (macro-to-submicro translation), PRIM-SCL004 (emergent property reasoning)
- **Depends on**: none (chapter opener)
- **Cross-chapter refs**: PRIM-COM001 (atomic composition, COM.1) ← backward
- **Est. pages**: 7
- **Key content**: Central cognitive operation of scale reasoning: bridging submicroscopic and macroscopic levels. Emergence — properties like boiling point exist only at the collective level. Crosses the "centralized to decentralized" threshold.

### SCL.2: How do you count atoms you cannot see?
- **Items introduced**: PRIM-SCL002 (mole concept), PRIM-SCL006 (unit analysis)
- **Depends on**: SCL.1
- **Cross-chapter refs**: PRIM-COM005 (chemical formula reading, COM.3) ← backward
- **Est. pages**: 8
- **Key content**: The mole as chemistry's counting unit — bridge from balanced equations to laboratory balances. Avogadro's number. Dimensional analysis as error detection. Real-world anchors: recipe scaling, medication dosing.

### SCL.3: How much is dissolved, and why does it matter?
- **Items introduced**: PRIM-SCL003 (concentration reasoning), DEF-SCL001 (molarity), DEF-SCL002 (parts per million/billion)
- **Depends on**: SCL.2
- **Cross-chapter refs**: DEF-STR004 ("like dissolves like," STR.4) ← backward
- **Est. pages**: 8
- **Key content**: Concentration as amount per volume. Molarity. PPM/PPB for trace-level concentrations. Dilution reasoning. Real-world anchors: lead in water, chlorine residual, IV preparation.

### SCL.4: How do ratios scale up to lab quantities?
- **Items introduced**: PRIM-SCL005 (proportional reasoning), DEF-SCL005 (safety and risk reasoning)
- **Depends on**: SCL.2, SCL.3
- **Cross-chapter refs**: none
- **Est. pages**: 7
- **Key content**: Proportional reasoning as the quantitative workhorse. Safety/risk reasoning: hazard vs. risk, reading an SDS, LD50 values. Real-world anchors: scaling a recipe, GHS pictograms.

### SCL.E: How do gases and solutions surprise us? (E)
- **Items introduced**: DEF-SCL003 (ideal gas reasoning) (E), DEF-SCL004 (colligative properties) (E)
- **Depends on**: SCL.1, SCL.2
- **Cross-chapter refs**: none
- **Est. pages**: 5
- **Key content**: Enrichment — ideal gas law (qualitative predictions only). Colligative properties as paradigm emergence: boiling point elevation and freezing point depression depend on particle count, not identity.

### SCL.CP-001: Why Does Rubbing Alcohol Evaporate Faster Than Water? (Capstone)
- **Pattern**: CP-001 (Structure-to-Property Prediction)
- **ADP**: ADP-001
- **Prerequisite domains**: STR (Ch 2) ✓, SCL (Ch 4) ✓
- **Est. pages**: 4
- **Bridge**: Why don't oil and water mix?

### SCL.CP-004: Why Is CO₂ a Greenhouse Gas but N₂ Is Not? (Capstone)
- **Pattern**: CP-004 (Greenhouse Effect)
- **ADP**: ADP-004
- **Prerequisite domains**: STR (Ch 2) ✓, NRG (Ch 3) ✓, SCL (Ch 4) ✓
- **Est. pages**: 4
- **Bridge**: Why is methane worse than CO₂ for climate?

---

## Chapter 5: What Happens? (CHG)

**Governing question**: What drives chemical transformations, what controls their rate and extent, and how do we classify them?

### CHG.1: How do we describe what happens in a reaction?
- **Items introduced**: PRIM-CHG001 (equation reading and balancing), PRIM-CHG002 (reaction type recognition)
- **Depends on**: none (chapter opener)
- **Cross-chapter refs**: PRIM-COM005 (formula reading, COM.3) ← backward; PRIM-COM006 (conservation, COM.3) ← backward; PRIM-STR001 (bond type, STR.1) ← backward
- **Est. pages**: 8
- **Key content**: Equation balancing as procedural deployment of atom conservation. Coefficients as mole ratios. Five reaction archetypes as pattern-matching tools for predicting products.

### CHG.2: How far does a reaction go?
- **Items introduced**: PRIM-CHG003 (equilibrium reasoning), DEF-CHG003 (Le Chatelier's principle)
- **Depends on**: CHG.1
- **Cross-chapter refs**: PRIM-SCL003 (concentration, SCL.3) ← backward; PRIM-NRG005 (spontaneity, NRG.3) ← backward
- **Est. pages**: 8
- **Key content**: Equilibrium as dynamic steady state. K as qualitative indicator (large = products favored). Le Chatelier's for predicting perturbation response. Qualitative only — no ICE tables, no Kc calculations.

### CHG.3: What controls how fast a reaction proceeds?
- **Items introduced**: PRIM-CHG004 (rate reasoning), DEF-CHG001 (catalyst)
- **Depends on**: CHG.2
- **Cross-chapter refs**: PRIM-NRG006 (activation energy, NRG.4) ← backward; PRIM-SCL003 (concentration, SCL.3) ← backward
- **Est. pages**: 7
- **Key content**: Separates "favorable" from "fast." Four rate factors (temperature, concentration, surface area, catalyst). Catalyst lowers Ea without being consumed. Enzyme preview. Real-world anchors: refrigerating food, catalytic converters, lactose intolerance.

### CHG.4: How do acids and bases interact?
- **Items introduced**: PRIM-CHG005 (acid-base reasoning), DEF-CHG002 (pH scale)
- **Depends on**: CHG.1
- **Cross-chapter refs**: PRIM-STR002 (bond polarity, STR.2) ← backward; PRIM-SCL003 (concentration, SCL.3) ← backward
- **Est. pages**: 7
- **Key content**: Bronsted acid-base framework. Conjugate pairs. Strong vs. weak acids. pH scale as compact 0-14 representation. No Ka/Kb calculations. Real-world anchors: antacids, pool pH, soil pH, blood pH.

### CHG.5: How do electrons drive chemical change?
- **Items introduced**: PRIM-CHG006 (oxidation-reduction reasoning)
- **Depends on**: CHG.1
- **Cross-chapter refs**: PRIM-COM007 (valence electrons, COM.2) ← backward
- **Est. pages**: 6
- **Key content**: Oxidation as electron loss, reduction as electron gain. Oxidizing/reducing agents. Oxidation number rules. Electron conservation. No half-reaction balancing. Real-world anchors: batteries, rusting, stainless steel.

### CHG.E: How is nuclear change different from chemical change? (E)
- **Items introduced**: PRIM-CHG007 (nuclear change reasoning) (E), DEF-CHG004 (half-life), DEF-CHG005 (precipitation) (E)
- **Depends on**: CHG.1, CHG.2
- **Cross-chapter refs**: DEF-COM001 (isotope, COM.4) ← backward; PRIM-STR001 (bond type, STR.1) ← backward; PRIM-SCL003 (concentration, SCL.3) ← backward
- **Est. pages**: 6
- **Key content**: Enrichment — nuclear change vs. chemical change (Z changes). Alpha, beta, gamma types. Half-life as environment-independent decay rate. Precipitation as specialized double replacement using solubility rules.
- **Note**: DEF-CHG004 (half-life) is listed Core in registry but depends on E-tier PRIM-CHG007; effectively E-tier in this architecture. DEF-CHG005 (precipitation) is an independent E-tier topic grouped here for pedagogical coherence.

### CHG.CP-002: Why Does a Battery Eventually Die? (Capstone)
- **Pattern**: CP-002 (Energy-Driven Transformation)
- **ADP**: ADP-002
- **Prerequisite domains**: NRG (Ch 3) ✓, CHG (Ch 5) ✓
- **Est. pages**: 4
- **Bridge**: Why does ice melt at room temperature?

### CHG.CP-003: Why Does Aspirin Hurt Your Stomach but an Antacid Helps? (Capstone)
- **Pattern**: CP-003 (Acid-Base in the Body)
- **ADP**: ADP-003
- **Prerequisite domains**: STR (Ch 2) ✓, CHG (Ch 5) ✓, SCL (Ch 4) ✓
- **Est. pages**: 4
- **Bridge**: Why does lemon juice taste sour but soap feels slippery?

### CHG.CP-005: Is Fluoride in Drinking Water Safe? (Capstone)
- **Pattern**: CP-005 (Dose Makes the Poison)
- **ADP**: ADP-005
- **Prerequisite domains**: STR (Ch 2) ✓, CHG (Ch 5) ✓, SCL (Ch 4) ✓
- **Est. pages**: 4
- **Bridge**: Is chlorine in pool water dangerous?

### CHG.CP-006: Why Do We Cook Food? (Capstone)
- **Pattern**: CP-006 (Food Chemistry)
- **ADP**: ADP-006
- **Prerequisite domains**: COM (Ch 1) ✓, NRG (Ch 3) ✓, CHG (Ch 5) ✓, SCL (Ch 4) ✓
- **Est. pages**: 4
- **Bridge**: Why do food labels list Calories?

---

## Chapter 6: Chemistry Meets Life (E-tier Capstone)

**Purpose**: Optional capstone deploying CP-007 (Biochemistry Connection). Entire chapter can be omitted without breaking any Core dependency.

### CH6.CP-007: Why Does DNA Have a Double Helix? (Capstone)
- **Pattern**: CP-007 (Biochemistry Connection)
- **ADP**: ADP-007
- **Prerequisite domains**: STR (Ch 2) ✓, CHG (Ch 5) ✓, SCL (Ch 4) ✓
- **Key items deployed**: DEF-STR008 (polymer reasoning), DEF-STR007 (carbon backbone), PRIM-STR004 (IMF hierarchy), PRIM-STR005 (structure-to-property), PRIM-CHG004 (rate reasoning), PRIM-SCL004 (emergent property)
- **Est. pages**: 10
- **Bridge**: Why do proteins fold into specific shapes?
- **Key content**: Extended deployment showing that the same chemical primitives explaining everyday phenomena (evaporation, dissolving) also explain the molecular basis of life. DNA double helix from hydrogen bonding. Protein folding from IMF hierarchy. Enzymatic catalysis as rate reasoning in biological context. Information storage as emergence.

---

## Front Matter (~6 pages)

- Preface: how to use this book, the reasoning-move approach
- "Your Chemical Toolkit" overview: the 5 domains as question-driven chapters
- Dependency diagram (visual version of the DAG)
- Notation guide (from notation concordance, 00-STRATEGIC-DECISIONS.md)

## Back Matter (~6 pages)

- Glossary of all 62 items with taxonomy IDs
- Index of real-world hooks by topic (food, health, environment, materials, energy)
- Selected answers to end-of-section questions

---

## Cross-Reference Catalog

### Cross-Domain Backward References

All references from later chapters to items defined in earlier chapters. Every entry is a **backward** reference (safe — no forward declarations needed).

| From Section | References | Defined In | Direction |
|-------------|-----------|------------|-----------|
| STR.1 | PRIM-COM007 (valence electrons) | COM.2 | Backward ✓ |
| STR.1 | DEF-COM005 (electronegativity) | COM.2 | Backward ✓ |
| STR.2 | DEF-COM005 (electronegativity) | COM.2 | Backward ✓ |
| STR.5 | PRIM-COM007 (valence electrons) | COM.2 | Backward ✓ |
| STR.E | DEF-COM002 (ion) | COM.4 | Backward ✓ |
| NRG.1 | PRIM-COM006 (conservation) | COM.3 | Backward ✓ |
| SCL.1 | PRIM-COM001 (atomic composition) | COM.1 | Backward ✓ |
| SCL.2 | PRIM-COM005 (formula reading) | COM.3 | Backward ✓ |
| SCL.3 | DEF-STR004 (like dissolves like) | STR.4 | Backward ✓ |
| CHG.1 | PRIM-COM005 (formula reading) | COM.3 | Backward ✓ |
| CHG.1 | PRIM-COM006 (conservation) | COM.3 | Backward ✓ |
| CHG.1 | PRIM-STR001 (bond type) | STR.1 | Backward ✓ |
| CHG.2 | PRIM-SCL003 (concentration) | SCL.3 | Backward ✓ |
| CHG.2 | PRIM-NRG005 (spontaneity) | NRG.3 | Backward ✓ |
| CHG.3 | PRIM-NRG006 (activation energy) | NRG.4 | Backward ✓ |
| CHG.3 | PRIM-SCL003 (concentration) | SCL.3 | Backward ✓ |
| CHG.4 | PRIM-STR002 (bond polarity) | STR.2 | Backward ✓ |
| CHG.4 | PRIM-SCL003 (concentration) | SCL.3 | Backward ✓ |
| CHG.5 | PRIM-COM007 (valence electrons) | COM.2 | Backward ✓ |
| CHG.E | DEF-COM001 (isotope) | COM.4 | Backward ✓ |
| CHG.E | PRIM-STR001 (bond type) | STR.1 | Backward ✓ |
| CHG.E | PRIM-SCL003 (concentration) | SCL.3 | Backward ✓ |

### Forward References

| Count | Status |
|-------|--------|
| 0 | **Zero forward references.** |

The linearization COM → STR → NRG → SCL → CHG eliminates all cross-chapter forward references. Within each chapter, section ordering by intra-domain dependency graph eliminates intra-chapter forward references.

### Potential Forward Previews (not references)

These are cases where an earlier chapter may briefly mention a concept that is formally introduced later. These are NOT forward references (the concept is not used or defined) but pedagogical foreshadowing:

| From | Previews | Formally Defined In | Treatment |
|------|----------|-------------------|-----------|
| STR.3 (IMF hierarchy) | "We will see that IMF strength determines boiling point" | SCL (Ch 4, via CP-001) | One-sentence forward note; no dependency |
| NRG.4 (activation energy) | "We will see how catalysts lower this barrier" | CHG.3 (catalyst definition) | One-sentence note: "Catalysts, which we'll meet in Ch 5, work by lowering the activation energy." |

These 1-2 forward notes are minor and do not create dependency violations.

---

## Item Placement Verification

Every taxonomy ID from CONVENTIONS.md Section 9 appears in exactly one section:

| Domain | Items | Placed In | All Accounted? |
|--------|-------|-----------|----------------|
| COM | 13 (8 PRIM + 5 DEF) | COM.1–COM.E | ✓ |
| STR | 15 (5 PRIM + 10 DEF) | STR.1–STR.E | ✓ |
| NRG | 11 (6 PRIM + 5 DEF) | NRG.1–NRG.E | ✓ |
| SCL | 11 (6 PRIM + 5 DEF) | SCL.1–SCL.E | ✓ |
| CHG | 12 (7 PRIM + 5 DEF) | CHG.1–CHG.E | ✓ |
| **Total** | **62** | **28 content sections** | **✓** |

All 7 CPs placed in 7 capstone sections. All 7 ADPs deployed.
