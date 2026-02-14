# DOMAIN-COM v0.1

## 0. Sources & Assumptions

- SRC-COM001: Tro, *Introductory Chemistry*, 6th ed., 2018, Ch. 2--5 (atoms, elements, compounds, nomenclature)
- SRC-COM002: IUPAC, *Compendium of Chemical Terminology* ("Gold Book"), 2019 online ed. (authoritative definitions of element, isotope, ion, electronegativity)
- SRC-COM003: Meijer et al., "Students' understanding of the structure of matter," *J. Chem. Educ.*, 2009 (misconceptions about the continuous/discrete threshold)
- SRC-GLB008: OpenStax, *Chemistry 2e*, 2019, Ch. 1--4
- SRC-GLB009: Zumdahl & Zumdahl, *Chemistry*, 10th ed., 2017, Ch. 1--3
- SRC-GLB010: ACS, *Chemistry in Context*, 10th ed., 2020, Ch. 1--2
- ASM-COM001: Students enter with no prior formal chemistry. All reasoning starts from the macroscopic observation that "stuff exists" and builds toward the atomic model. Justification: the non-majors population is heterogeneous; assuming zero chemistry background is the only safe floor.
- ASM-COM002: The atomic model is accepted as given (atoms exist, are composed of protons/neutrons/electrons). We do not derive the atomic model from experimental evidence; we state it and use it. Justification: historical derivation (cathode rays, oil drop, gold foil) is a history-of-science enrichment, not a reasoning prerequisite for chemical literacy (SRC-GLB010, Ch. 1).

## 1. Domain Intent

- **Governing question**: What is stuff made of, and how do we identify it?
- **Scope**: Identifying the building blocks of matter (atoms, elements, compounds), counting and classifying them, reading chemical formulas, and determining how many valence electrons an atom contributes. COM provides the identity layer: what atoms are present, how many, and what element each belongs to.
- **Non-goals**: How atoms connect or arrange in three dimensions (STR). Why processes occur or whether they are energetically favorable (NRG). How substances transform into other substances (CHG). How to bridge molecular-level descriptions to macroscopic measurements (SCL).
- **Dissolution argument**: Composition answers WHAT (identity, classification, counting). Structure answers HOW (3D arrangement, bond angles, molecular shape). You can know a substance contains C, H, and O (composition) without knowing its molecular shape or bond polarities (structure). A mass spectrometer gives composition; an X-ray crystallographer gives structure. Merging COM into STR would conflate "what are the building blocks" with "how are they arranged" -- two cognitively distinct operations that students routinely confuse (SRC-COM003). Keeping them separate forces students to recognize which question they are answering. Similarly, COM cannot merge into CHG because knowing what a substance is made of does not tell you what it reacts with or how fast.
- **Threshold schema mapping**: Continuous --> Discrete. The foundational conceptual shift in COM is recognizing that matter is not continuous stuff but is composed of discrete, countable atoms. Every COM primitive operates on discrete entities (atoms, protons, electrons, formula units). Students who fail to cross this threshold treat matter as infinitely divisible and cannot reason about conservation of atoms or formula ratios.

## 2. Prerequisites

COM is the root domain. It imports nothing from STR, NRG, CHG, or SCL. All other domains depend on COM (directly or transitively). No DEP entries exist for this domain.

## 3. Primitives

- PRIM-COM001: **Atomic composition analysis**
  - Reasoning move: Given a substance or sample description, decompose it into constituent atoms and identify their subatomic particles (protons, neutrons, electrons) to determine what the substance is made of at the most fundamental chemical level.
  - Description: The cognitive operation of taking any macroscopic sample and reasoning downward to its atomic constituents. This is the entry point to all chemical reasoning: before you can ask about structure, energy, or change, you must know what atoms are present. The operation includes recognizing that atoms are the smallest unit retaining elemental identity and that each atom contains a nucleus (protons + neutrons) surrounded by electrons.
  - Semi-formal: Given a substance S, identify the set of atom types {A_1, A_2, ..., A_n} present. For each atom type A_i, specify: Z_i (proton count), mass number (protons + neutrons), and electron count. Atom identity is determined by Z_i alone.
  - Depends: none (foundational -- this is the root primitive of the entire taxonomy)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 2), SRC-GLB009 (Zumdahl Ch. 2), SRC-COM001 (Tro Ch. 2)
  - Referenced by: STR, NRG, SCL, CHG
  - Tier: C
  - Real-world hook: When a food label lists "sodium" in the ingredients, you are performing atomic composition analysis at a basic level -- identifying which element is present. When a water quality report says "lead detected at 5 ppb," the first reasoning step is: lead atoms are in the water.

- PRIM-COM002: **Elemental identity**
  - Reasoning move: Given an atom's proton count (atomic number Z), identify the element it belongs to and locate it on the periodic table to access that element's characteristic properties.
  - Description: The cognitive operation that links the abstract concept of "proton count" to a named element with a specific position on the periodic table. This is the lookup step: Z = 6 means carbon, period 2, group 14. Elemental identity is absolute -- it depends only on Z, not on neutron count, charge, or bonding state. This primitive establishes that the periodic table is a map indexed by Z.
  - Semi-formal: Given Z (number of protons), there exists exactly one element E such that E = PeriodicTable(Z). The element's symbol, name, row (period), and column (group) are determined by Z. Two atoms with the same Z are the same element regardless of neutron count or electron count.
  - Depends: PRIM-COM001 (atomic composition analysis -- must know what an atom is and what Z means)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 2), SRC-COM002 (IUPAC Gold Book, "element")
  - Referenced by: STR, NRG
  - Tier: C
  - Real-world hook: When a news headline says "mercury found in fish," you can look up mercury (Z = 80) on the periodic table to learn it is a heavy metal in group 12 -- that one lookup tells you it is fundamentally different from lighter elements like calcium (Z = 20).

- PRIM-COM003: **Periodic position reasoning**
  - Reasoning move: Given an element's row (period) and column (group) on the periodic table, predict its relative atomic size, electronegativity, ionization energy, and typical reactivity pattern compared to neighboring elements.
  - Description: The cognitive operation of extracting qualitative predictions from periodic table position. This is the single most powerful reasoning shortcut in introductory chemistry: position predicts properties. Left-to-right across a period, atoms get smaller and more electronegative; top-to-bottom down a group, atoms get larger and less electronegative. These trends arise from nuclear charge and electron shielding but are deployed as pattern-based reasoning moves, not derived from quantum mechanics.
  - Semi-formal: For elements E_a and E_b: if same period and group(E_a) < group(E_b), then size(E_a) > size(E_b) and electronegativity(E_a) < electronegativity(E_b). If same group and period(E_a) < period(E_b), then size(E_a) < size(E_b) and electronegativity(E_a) > electronegativity(E_b). Reactivity trends differ for metals (increases down a group) vs. nonmetals (increases up a group).
  - Depends: PRIM-COM002 (elemental identity -- must locate the element on the table first)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 3), SRC-GLB009 (Zumdahl Ch. 2), SRC-COM001 (Tro Ch. 3)
  - Referenced by: STR, NRG
  - Tier: C
  - Real-world hook: Lithium, sodium, and potassium are all in group 1. Periodic position reasoning predicts they all react vigorously with water, with potassium reacting most violently -- which is why potassium supplements come in carefully controlled doses, not as pure metal.

- PRIM-COM004: **Substance classification**
  - Reasoning move: Given a sample description or chemical formula, classify it as an element (one type of atom), compound (two or more types of atoms chemically bonded), or mixture (two or more substances physically combined) to determine what separation or analysis methods are appropriate.
  - Description: The cognitive operation of categorizing matter into its three fundamental types based on composition. This is the first decision branch in any analysis of a sample: is it pure or mixed? If pure, is it an element or compound? The classification determines what you can and cannot do: elements cannot be chemically decomposed; compounds can; mixtures can be separated by physical means. This is a composition question (WHAT is in the sample), not a structure question (HOW is it arranged).
  - Semi-formal: Given sample S: if S contains only one type of atom and those atoms are not bonded to atoms of another type, S is an element. If S contains two or more types of atoms chemically bonded in fixed ratios, S is a compound. If S contains two or more substances not chemically bonded, S is a mixture. Classification is exhaustive and mutually exclusive for pure substances vs. mixtures.
  - Depends: PRIM-COM001 (atomic composition analysis -- must identify what atoms are present)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 1), SRC-COM001 (Tro Ch. 3)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: Tap water is a mixture (water + dissolved minerals + dissolved gases). Table salt (NaCl) is a compound. The aluminum in a soda can is an element. Knowing which category a sample falls into tells you whether filtering, distilling, or a chemical reaction is needed to separate its components.

- PRIM-COM005: **Chemical formula reading**
  - Reasoning move: Given a chemical formula (molecular, ionic, or empirical), extract which atoms are present, how many of each, and their ratios to determine the quantitative composition of the substance.
  - Description: The cognitive operation of decoding chemical notation into atom counts. A formula like C6H12O6 means: 6 carbon atoms, 12 hydrogen atoms, 6 oxygen atoms per formula unit. This primitive is purely about reading and counting -- it does not address how the atoms are arranged (STR) or what the substance does (CHG). It includes reading subscripts, parenthetical groupings like Ca(OH)2, and coefficients in balanced equations.
  - Semi-formal: Given formula F, parse F into a set of (element, count) pairs: {(E_1, n_1), (E_2, n_2), ...} where each n_i is the number of atoms of element E_i per formula unit. For parenthetical groups, multiply subscripts: Ca(OH)2 = {(Ca, 1), (O, 2), (H, 2)}.
  - Depends: PRIM-COM001 (atomic composition analysis), PRIM-COM002 (elemental identity -- must recognize element symbols)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 2), SRC-GLB009 (Zumdahl Ch. 2)
  - Referenced by: SCL, CHG
  - Tier: C
  - Real-world hook: The ingredient "sodium bicarbonate (NaHCO3)" on a baking soda box encodes composition: 1 sodium, 1 hydrogen, 1 carbon, 3 oxygen atoms per formula unit. Reading a formula is the gateway to understanding what is in any chemical product.

- PRIM-COM006: **Conservation of atoms**
  - Reasoning move: Given a before-and-after scenario (a chemical reaction, a physical change, or a claim about matter), verify that atom counts are preserved -- atoms rearrange but are neither created nor destroyed.
  - Description: The cognitive operation of applying the conservation principle to matter at the atomic level. This is the chemistry-specific form of conservation: in any chemical process, the total number of each type of atom on the reactant side equals the total number on the product side. This primitive is the foundation for equation balancing (CHG) and stoichiometric reasoning (SCL), but at the COM level it is simply the verification step: did atoms balance?
  - Semi-formal: For any chemical process with reactants R and products P: for every element E, count(E in R) = count(E in P). No atom of any element is created or destroyed. Nuclear reactions (PRIM-CHG007, Enrichment) are the only exception, and they are flagged as such.
  - Depends: PRIM-COM001 (atomic composition analysis -- must count atoms)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 4), SRC-GLB009 (Zumdahl Ch. 3), SRC-COM002 (IUPAC Gold Book, "conservation of mass")
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: When wood burns, it seems to disappear. Conservation of atoms says the carbon and hydrogen atoms are still there -- they combined with oxygen to form CO2 and H2O that escaped as gas. The ash is what remains of the non-volatile atoms. Nothing was destroyed; everything was rearranged.

- PRIM-COM007: **Valence electron reasoning**
  - Reasoning move: Given an element's group number on the periodic table, determine its valence electron count and predict its typical bonding behavior (how many bonds it tends to form or how many electrons it tends to gain or lose).
  - Description: The cognitive operation of connecting periodic table position to the electron-level explanation of bonding capacity. Main-group elements have valence electron counts equal to their group number (groups 1--2) or group number minus 10 (groups 13--18). The octet rule -- atoms tend to gain, lose, or share electrons to achieve 8 valence electrons (2 for hydrogen) -- provides a simple predictive framework for bonding behavior. This primitive lives in COM because it is about counting electrons based on identity (periodic position), not about the 3D arrangement of bonds (STR).
  - Semi-formal: For main-group element E in group G: valence electrons = G (for G = 1, 2) or G - 10 (for G = 13--18). Bonds formed approximately = 8 - valence electrons (for nonmetals) or = valence electrons lost (for metals). Exception: hydrogen targets 2, not 8.
  - Depends: PRIM-COM002 (elemental identity), PRIM-COM003 (periodic position reasoning -- group number determines valence count)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 3), SRC-COM001 (Tro Ch. 4)
  - Referenced by: STR, CHG
  - Tier: C
  - Real-world hook: Carbon is in group 14, so it has 4 valence electrons and typically forms 4 bonds. This is why carbon can build the complex molecular scaffolding of life -- from sugars to DNA to plastics. Knowing valence count from group number is the first step to understanding why carbon is so versatile.

- PRIM-COM008: **Causal chain reasoning**
  - Reasoning move: Given a chemical claim ("X causes Y"), identify the causal chain: what molecular-level event leads to what macroscopic observation, through what intermediate steps, and whether the claimed causation is supported or merely correlational.
  - Description: The meta-reasoning skill of decomposing cause-and-effect claims into mechanistic steps. This is not specific to any one chemical topic -- it is the transferable analytical move that connects submicroscopic events to macroscopic observations. When someone claims "BPA in plastic bottles causes health problems," causal chain reasoning asks: what molecular interaction does BPA have? Through what biological pathway? At what concentration? This primitive is owned by COM because it is foundational to all chemical reasoning, not because it is about composition specifically. It is the reasoning move that chains together primitives from different domains.
  - Semi-formal: Given a claim "A causes B," decompose into: (1) molecular-level event at A, (2) mechanism by which A's molecular event propagates, (3) intermediate steps, (4) macroscopic observation B. Evaluate: is each link supported by evidence? Is the chain complete, or are steps missing? Is the relationship causal or merely correlational?
  - Depends: none (meta-reasoning skill -- foundational, cross-cutting)
  - Ownership: COM
  - Source: SRC-GLB001 (Talanquer 2006, causality dimension), SRC-GLB006 (Bennett et al. 2007, bridging activities)
  - Referenced by: STR, NRG, CHG, SCL
  - Tier: C
  - Real-world hook: A shampoo label claims "sulfate-free for healthier hair." Causal chain reasoning asks: what do sulfates do at the molecular level (they are surfactants that strip oils)? Is "stripping oils" always harmful? For whom? The claim collapses without a complete causal chain from molecular mechanism to health outcome.

## 4. Definitions

- DEF-COM001: **Isotope**
  - Reasoning move: Given two atoms of the same element (same Z) with different mass numbers, recognize them as isotopes -- same chemical behavior, different mass, potentially different nuclear stability.
  - Description: An isotope is a variant of an element with the same number of protons but a different number of neutrons. Isotopes have identical chemical properties (because chemistry depends on electrons, which depend on Z) but different masses and potentially different nuclear stabilities (some isotopes are radioactive). This definition is built from elemental identity (same Z = same element) and atomic composition analysis (different neutron count = different mass number).
  - Semi-formal: Atoms A and B are isotopes of element E if and only if Z(A) = Z(B) and mass_number(A) != mass_number(B). Chemical behavior of A and B is identical; nuclear stability may differ.
  - Depends: PRIM-COM001 (atomic composition analysis -- neutron count), PRIM-COM002 (elemental identity -- same Z = same element)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 2), SRC-COM002 (IUPAC Gold Book, "isotope")
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: Carbon-12 and carbon-14 are isotopes. Carbon-14 is radioactive and is used in archaeological dating. The carbon in your food and the carbon-14 used to date ancient artifacts are the same element with the same chemistry -- just different neutron counts.

- DEF-COM002: **Ion**
  - Reasoning move: Given an atom or group of atoms with a net electric charge (from gaining or losing electrons), recognize it as an ion and predict its charge from periodic position.
  - Description: An ion is an atom or polyatomic group that has gained or lost one or more electrons, giving it a net positive (cation) or negative (anion) charge. Metals tend to lose electrons (form cations); nonmetals tend to gain electrons (form anions). The charge is predictable from periodic position: group 1 metals form +1 ions, group 2 form +2, group 17 nonmetals form -1, group 16 form -2. This definition bridges composition (what charge does this atom carry?) to structure (how do ions bond?).
  - Semi-formal: An ion is an atom or group with electron count != proton count. If electrons < protons, charge = +(protons - electrons) (cation). If electrons > protons, charge = -(electrons - protons) (anion). For main-group elements: predicted cation charge = group number (groups 1--2); predicted anion charge = group number - 18 (groups 15--17).
  - Depends: PRIM-COM001 (atomic composition analysis -- electron count vs. proton count), PRIM-COM003 (periodic position reasoning -- group predicts charge)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 2), SRC-COM002 (IUPAC Gold Book, "ion")
  - Referenced by: STR, CHG
  - Tier: C
  - Real-world hook: Sports drinks advertise "electrolytes" -- these are dissolved ions (Na+, K+, Cl-) that conduct electricity in your body and regulate nerve signals. The periodic table predicts that sodium (group 1) forms Na+ and chlorine (group 17) forms Cl-.

- DEF-COM003: **Molecular vs. empirical formula**
  - Reasoning move: Given composition data for a compound, distinguish between the molecular formula (actual atom count per molecule) and the empirical formula (simplest whole-number ratio of atoms) and determine which one is available from the analytical method used.
  - Description: The molecular formula gives the true number of each atom in one molecule (e.g., C6H12O6 for glucose). The empirical formula gives the simplest ratio (e.g., CH2O for glucose). Multiple compounds can share the same empirical formula but have different molecular formulas. The distinction matters because some analytical methods (e.g., combustion analysis) yield only empirical formulas; determining the molecular formula requires additional information (molar mass). This is a composition concept -- it is about counting atoms, not about how they are arranged.
  - Semi-formal: For a compound with molecular formula C_a H_b O_c, the empirical formula is C_(a/d) H_(b/d) O_(c/d) where d = GCD(a, b, c). Molecular formula = (empirical formula) x n, where n = molar_mass / empirical_formula_mass. If n = 1, the two formulas are identical.
  - Depends: PRIM-COM005 (chemical formula reading -- must read and extract atom counts)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 3), SRC-GLB009 (Zumdahl Ch. 3)
  - Referenced by: SCL
  - Tier: E
  - Real-world hook: Formaldehyde (CH2O), acetic acid (C2H4O2), and glucose (C6H12O6) all have the same empirical formula CH2O, but they are vastly different substances. A lab test that gives only the ratio cannot distinguish them -- you need molar mass to get the molecular formula.

- DEF-COM004: **Percent composition**
  - Reasoning move: Given a chemical formula, calculate the mass fraction (percent by mass) of each element in the compound to connect formula-level composition to mass-level measurements.
  - Description: Percent composition is the bridge from atom counts (discrete, microscopic) to mass fractions (continuous, macroscopic). For each element in a formula, multiply its atom count by its atomic mass, divide by the total formula mass, and multiply by 100. This is the reverse of determining empirical formulas from experimental data: percent composition goes from formula to mass fractions; empirical formula determination goes from mass fractions to formula. Percent composition lives in COM because it is about what fraction of the mass each element contributes -- a composition question, not a structure or scale question.
  - Semi-formal: For compound with formula E_1(n_1) E_2(n_2) ..., percent composition of E_i = (n_i x atomic_mass(E_i)) / formula_mass x 100%. Sum of all percent compositions = 100%.
  - Depends: PRIM-COM005 (chemical formula reading -- extract atom counts), DEF-COM003 (molecular vs. empirical formula -- percent composition is the same for molecular and empirical forms)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 3), SRC-GLB009 (Zumdahl Ch. 3)
  - Referenced by: SCL
  - Tier: E
  - Real-world hook: A nutrition label says a serving of milk contains "30% of daily calcium." Percent composition reasoning tells you what fraction of the calcium compound's mass is actually calcium. In calcium carbonate (CaCO3), calcium is only 40% of the mass -- the rest is carbon and oxygen.

- DEF-COM005: **Electronegativity**
  - Reasoning move: Given two elements' periodic table positions, compare their electronegativities to predict which atom will attract shared electrons more strongly in a bond between them.
  - Description: Electronegativity is a periodic trend: the ability of an atom to attract shared electrons in a chemical bond. It increases left-to-right across a period (higher nuclear charge, same shielding) and decreases top-to-bottom down a group (more shielding from inner electrons). Fluorine is the most electronegative element; francium is the least. COM owns electronegativity as a periodic trend -- it is a property derived from periodic position reasoning. STR imports electronegativity to determine bond polarity (whether electrons are shared equally or unequally). The ownership split is clean: COM says "this atom attracts electrons more strongly"; STR says "therefore, the bond is polar and the molecule has a certain shape consequence."
  - Semi-formal: Electronegativity EN is a function of periodic position: EN increases with group number (left to right) and decreases with period number (top to bottom). For atoms A and B, delta-EN = |EN(A) - EN(B)|. If delta-EN approx 0, the bond is nonpolar. If delta-EN is moderate, the bond is polar. If delta-EN is large, the bond is ionic. Exact thresholds are empirical, not rigidly defined.
  - Depends: PRIM-COM003 (periodic position reasoning -- electronegativity is a periodic trend)
  - Ownership: COM
  - Source: SRC-GLB008 (OpenStax Ch. 3), SRC-COM002 (IUPAC Gold Book, "electronegativity"), SRC-GLB009 (Zumdahl Ch. 2)
  - Referenced by: STR
  - Tier: C
  - Real-world hook: Oxygen (EN = 3.44) is far more electronegative than hydrogen (EN = 2.20). This difference is why water molecules are polar, which is why water dissolves salt, which is why the oceans are salty. The electronegativity trend from the periodic table is the first domino in that causal chain.

## 5. Contested Concepts

The primary contested boundary for COM is with STR. Three concepts require explicit ownership resolution:

| Concept | COM Version (Owner) | STR Version (If Any) | Resolution |
|---------|---------------------|----------------------|------------|
| Molecular formula | PRIM-COM005 owns formula reading (identity, counting, ratios) | STR does not own; STR receives atom counts from COM | Boundary principle P1: counting atoms without geometry is COM. No conflict. |
| Lewis structure | COM provides the electron count via PRIM-COM007 (valence electrons) | DEF-STR001 owns the Lewis structure (arrangement of electrons around atoms) | Clean split: COM counts valence electrons (how many?); STR arranges them (where do they go?). |
| Electronegativity | DEF-COM005 owns the periodic trend (which atom attracts electrons more?) | STR imports DEF-COM005 to determine bond polarity (PRIM-STR002) | Boundary principle P1: electronegativity as a periodic property is identity/classification (COM). Bond polarity as a structural consequence is arrangement (STR). |

No contested concepts exist between COM and NRG, CHG, or SCL. COM's items are strictly about identity and counting, which do not overlap with energy accounting (NRG), transformation mechanics (CHG), or measurement bridging (SCL).

## 6. Real-World Hooks

| ID | Concept | Everyday Application |
|----|---------|---------------------|
| PRIM-COM001 | Atomic composition analysis | Reading a water quality report that lists detected elements (lead, arsenic, fluoride) |
| PRIM-COM002 | Elemental identity | Looking up an element from a news article ("radon in basements") on the periodic table |
| PRIM-COM003 | Periodic position reasoning | Understanding why lithium, sodium, and potassium batteries exist but not beryllium batteries (group 1 vs. group 2 reactivity) |
| PRIM-COM004 | Substance classification | Recognizing that "mineral water" is a mixture, "distilled water" is a compound, and "copper wire" is an element |
| PRIM-COM005 | Chemical formula reading | Decoding ingredient labels: "sodium bicarbonate (NaHCO3)" means 1 Na, 1 H, 1 C, 3 O |
| PRIM-COM006 | Conservation of atoms | Understanding that burning gasoline does not destroy matter -- the carbon atoms become CO2, which is why cars produce greenhouse gas |
| PRIM-COM007 | Valence electron reasoning | Explaining why neon signs glow (noble gases have full valence shells) and why sodium metal is violently reactive (one lonely valence electron) |
| PRIM-COM008 | Causal chain reasoning | Evaluating a news claim: "fluoride in water causes health problems" -- tracing the chain from molecular mechanism to claimed effect |
| DEF-COM001 | Isotope | Understanding carbon-14 dating in archaeology or iodine-131 in thyroid treatment |
| DEF-COM002 | Ion | Knowing what "electrolytes" in sports drinks actually are (dissolved ions: Na+, K+, Cl-) |
| DEF-COM003 | Molecular vs. empirical formula | Recognizing that different substances can share the same simplest ratio (CH2O is both formaldehyde and glucose's empirical formula) |
| DEF-COM004 | Percent composition | Comparing calcium supplements: calcium carbonate is only 40% calcium by mass, calcium citrate is only 21% |
| DEF-COM005 | Electronegativity | Understanding why water is such a good solvent (large O-H electronegativity difference makes water polar) |

## 7. Intra-Domain Dependency Graph

```
PRIM-COM001 (Atomic composition analysis)   PRIM-COM008 (Causal chain reasoning)
     |                                         [independent -- no intra-domain deps]
     +---> PRIM-COM002 (Elemental identity)
     |          |
     |          +---> PRIM-COM003 (Periodic position reasoning)
     |          |          |
     |          |          +---> PRIM-COM007 (Valence electron reasoning)
     |          |          +---> DEF-COM005 (Electronegativity)
     |          |          +---> DEF-COM002 (Ion)
     |          |
     |          +---> PRIM-COM005 (Chemical formula reading)
     |                     |
     |                     +---> DEF-COM003 (Molecular vs. empirical formula)
     |                     |          |
     |                     |          +---> DEF-COM004 (Percent composition)
     |                     |
     |                     +---> [also depends on PRIM-COM001]
     |
     +---> PRIM-COM004 (Substance classification)
     +---> PRIM-COM006 (Conservation of atoms)
     +---> DEF-COM001 (Isotope) [also depends on PRIM-COM002]
```

**Acyclicity verification**: All arrows point downward or laterally from items with lower numbers to items with higher numbers (with PRIM-COM008 isolated). No item depends on an item listed after it, except through explicitly noted shared dependencies. The graph is a DAG.

## 8. Cross-Domain Interface

### Exports

| ID | Concept | Imported by |
|----|---------|-------------|
| PRIM-COM001 | Atomic composition analysis | STR, NRG, SCL, CHG |
| PRIM-COM002 | Elemental identity | STR, NRG |
| PRIM-COM003 | Periodic position reasoning | STR, NRG |
| PRIM-COM004 | Substance classification | CHG |
| PRIM-COM005 | Chemical formula reading | SCL, CHG |
| PRIM-COM006 | Conservation of atoms | CHG |
| PRIM-COM007 | Valence electron reasoning | STR, CHG |
| PRIM-COM008 | Causal chain reasoning | STR, NRG, CHG, SCL |
| DEF-COM001 | Isotope | CHG |
| DEF-COM002 | Ion | STR, CHG |
| DEF-COM003 | Molecular vs. empirical formula | SCL |
| DEF-COM004 | Percent composition | SCL |
| DEF-COM005 | Electronegativity | STR |

### Imports

None. COM is the root domain and imports nothing from any other domain.

## 9. Difficulty Tiers

| ID | Concept | Tier | Justification |
|----|---------|------|---------------|
| PRIM-COM001 | Atomic composition analysis | C | Foundational: every subsequent concept requires knowing what atoms are present |
| PRIM-COM002 | Elemental identity | C | Core lookup skill: periodic table navigation is essential for all chemical reasoning |
| PRIM-COM003 | Periodic position reasoning | C | Core predictive tool: periodic trends are the most powerful shortcut in introductory chemistry |
| PRIM-COM004 | Substance classification | C | Core categorization: element/compound/mixture distinction governs all separation and analysis reasoning |
| PRIM-COM005 | Chemical formula reading | C | Core literacy: formulas are the universal language of chemistry; reading them is non-negotiable |
| PRIM-COM006 | Conservation of atoms | C | Core law: atom conservation underpins equation balancing, stoichiometry, and all change reasoning |
| PRIM-COM007 | Valence electron reasoning | C | Core bridge to STR: without valence counts, bonding reasoning (STR) cannot begin |
| PRIM-COM008 | Causal chain reasoning | C | Core meta-skill: the transferable reasoning move that connects molecular events to macroscopic claims |
| DEF-COM001 | Isotope | C | Core definition: needed for understanding radioactivity (CHG), medical imaging, and carbon dating |
| DEF-COM002 | Ion | C | Core definition: needed for ionic bonding (STR), electrolyte reasoning, and acid-base chemistry (CHG) |
| DEF-COM003 | Molecular vs. empirical formula | E | Enrichment: the distinction is important but not required for downstream Core items; omitting it does not break any dependency chain |
| DEF-COM004 | Percent composition | E | Enrichment: useful quantitative skill but no Core item in any domain depends on it; DEF-COM004 depends on DEF-COM003 (also E), maintaining tier consistency |
| DEF-COM005 | Electronegativity | C | Core definition: STR's bond polarity reasoning (PRIM-STR002, Core) imports this directly |

**Tier constraint verification**: No Enrichment item is a prerequisite for any Core item. DEF-COM003 (E) is referenced only by SCL and DEF-COM004 (E). DEF-COM004 (E) is referenced only by SCL. The Core tier alone forms a self-contained, dependency-complete sub-taxonomy of 11 items.

## 10. Self-Audit Checklist

- [x] Every PRIM has: reasoning move formulation ("Given X, do Y to determine Z"), description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [x] Every DEF depends only on previously listed PRIM/DEF (check intra-domain dependency graph)
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in the source domain's exports (N/A -- COM has no imports; COM's exports are listed and match the Primitive Registry in CONVENTIONS.md Section 9)
- [x] Dissolution argument is present and non-trivial (at least 2 sentences explaining why COM is distinct from STR, NRG, CHG, and SCL)
- [x] Real-world hooks cover everyday non-major contexts (water quality, food labels, sports drinks, news articles, household products, supplements)
- [x] Intra-domain dependency graph is acyclic (verified: all edges point from lower to higher in the numbering; PRIM-COM008 is independent)
- [x] Tier annotations (C/E) are present on all 13 items
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry in CONVENTIONS.md Section 9)
- [x] Reasoning moves are genuinely "Given X, do Y" cognitive operations (not mere topic labels or vocabulary words)
