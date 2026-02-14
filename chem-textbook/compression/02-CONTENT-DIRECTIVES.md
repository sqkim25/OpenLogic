# Phase 3: Content Directives

**Date:** 2026-02-14
**Depends on:** 00-STRATEGIC-DECISIONS.md (decisions 1-5, notation concordance), 01-CHAPTER-ARCHITECTURE.md (section assignments)
**Purpose:** Per-item directives for all 62 taxonomy items + 7 CP deployment directives. Each entry specifies the action, source, depth, reasoning-move framing, and licensing for Phase 4 writers.

---

## Action Decision Tree

For each taxonomy item, the following tree determines the action:

1. Is this PRIM-COM008 (causal chain reasoning)? → **WRITE-ORIGINAL** (META — no standalone source section)
2. Is the canonical source NC-SA licensed (CLUE or SAY)? → **WRITE-ORIGINAL** (preserve CC-BY 4.0 for textbook)
3. Does the item benefit from combining 2+ sources (OS content + CLUE reasoning framing)? → **SYNTHESIZE**
4. Was the Phase 2 signal for the canonical OS section REWRITE? → **REWRITE**
5. Was the Phase 2 signal ADAPT? → **ADAPT**
6. Remaining → **ADAPT** (default)

For composition patterns: Action is always **DEPLOY-CP** (uses ADP template).

Out-of-scope topics (16 documented in Phase 2 `05-GAP-ANALYSIS.md` §1b) do NOT receive directives — they are not taxonomy items.

---

## Action Distribution Summary

| Action | Count | Items |
|--------|-------|-------|
| **ADAPT** | 40 | Most OS-canonical items at appropriate non-majors depth |
| **REWRITE** | 11 | OS items requiring depth simplification (strip quantitative content) |
| **SYNTHESIZE** | 5 | Items benefiting from OS content + CLUE pedagogical framing |
| **WRITE-ORIGINAL** | 6 | META status (1) + NC-SA canonical (5) |
| **DEPLOY-CP** | 7 | One per composition pattern (CP-001 through CP-007) |
| **Total** | **69** | 62 taxonomy items + 7 CP deployments |

### Licensing Distribution

| License Status | Count |
|----------------|-------|
| CC-BY 4.0 clean | 51 |
| SYNTHESIZE OS-base | 5 |
| WRITE-ORIGINAL clean-room | 6 |
| DEPLOY-CP (original) | 7 |

### Depth Distribution

| Depth | Count |
|-------|-------|
| FULL | 38 |
| CONCEPTUAL-ONLY | 13 |
| STRIPPED-QUANTITATIVE | 11 |

---

## COM Domain Directives (13 items) + STR Domain Directives (15 items)

---

## Chapter COM: Composition -- What Is Stuff Made Of?

---

### PRIM-COM001: Atomic Composition Analysis
- **Target section**: COM.1
- **Action**: REWRITE
- **Canonical source**: OS 2.1--2.3 (CC-BY 4.0)
- **Supplementary sources**: Tro Ch. 2 (reference only); IUPAC Gold Book, "atom" (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a substance or sample description, decompose it into constituent atoms and identify their subatomic particles (protons, neutrons, electrons) to determine what the substance is made of at the most fundamental chemical level."
- **Real-world hook**: "When a water quality report lists 'lead detected at 5 ppb,' the first reasoning step is: lead atoms are in the water. Reading a food label that lists 'sodium' is performing atomic composition analysis at a basic level."
- **Licensing**: CC-BY 4.0 clean (OS base, rewritten)
- **Notes**: Phase 2 signal is ADAPT/REWRITE; select REWRITE because this is the root primitive and must set the tone and conceptual framing for the entire textbook. Establish the continuous-to-discrete threshold schema explicitly: matter is not infinitely divisible goo but is composed of countable atoms. Do NOT derive the atomic model historically (no cathode ray, oil drop, or gold foil experiments); state the model and use it. Introduce protons, neutrons, electrons as a simple inventory. Keep the treatment conversational and avoid jargon beyond the three subatomic particles. This section must land the idea that "before you can ask any chemistry question, you must first know what atoms are present."

---

### PRIM-COM002: Elemental Identity
- **Target section**: COM.1
- **Action**: ADAPT
- **Canonical source**: OS 2.3, 2.5 (CC-BY 4.0)
- **Supplementary sources**: IUPAC Gold Book, "element" (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given an atom's proton count (atomic number Z), identify the element it belongs to and locate it on the periodic table to access that element's characteristic properties."
- **Real-world hook**: "When a news headline says 'mercury found in fish,' you can look up mercury (Z = 80) on the periodic table to learn it is a heavy metal in group 12 -- fundamentally different from lighter elements like calcium (Z = 20)."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Frame the periodic table as a lookup map indexed by Z. Emphasize the absolute nature of elemental identity: Z alone determines the element, regardless of neutron count (isotopes) or electron count (ions). Teach students to navigate the table by row (period) and column (group). Keep the treatment short -- this is a lookup skill, not a concept requiring deep explanation. Pair with PRIM-COM001 in the same section so that students see the flow: identify atoms, then look each one up.

---

### PRIM-COM003: Periodic Position Reasoning
- **Target section**: COM.2
- **Action**: ADAPT
- **Canonical source**: OS 2.5, 6.5 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 2 (reference only); CLUE reasoning framing on periodic trends (reference only, CC-BY-NC-SA -- do not adapt text)
- **Depth**: FULL
- **Reasoning-move framing**: "Given an element's row (period) and column (group) on the periodic table, predict its relative atomic size, electronegativity, ionization energy, and typical reactivity pattern compared to neighboring elements."
- **Real-world hook**: "Lithium, sodium, and potassium are all in group 1. Periodic position reasoning predicts they all react vigorously with water, with potassium reacting most violently -- which is why potassium supplements come in carefully controlled doses, not as pure metal."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Treat periodic trends as pattern-based reasoning shortcuts, not quantum-mechanical derivations. Students need only the qualitative directions: left-to-right = smaller atoms, higher electronegativity; top-to-bottom = larger atoms, lower electronegativity. Strip ionization energy to a one-sentence mention (it parallels electronegativity direction); do not quantify it. Use a simple arrow-overlay diagram of the periodic table showing trend directions. Avoid the phrase "effective nuclear charge" -- instead say "the pull from the nucleus gets stronger across a row because more protons are added while the inner electron shield stays roughly the same."

---

### DEF-COM005: Electronegativity
- **Target section**: COM.2
- **Action**: ADAPT
- **Canonical source**: OS 6.5 (CC-BY 4.0)
- **Supplementary sources**: IUPAC Gold Book, "electronegativity" (reference only); Pauling, *The Nature of the Chemical Bond*, Ch. 3 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given two elements' periodic table positions, compare their electronegativities to predict which atom will attract shared electrons more strongly in a bond between them."
- **Real-world hook**: "Oxygen (EN = 3.44) is far more electronegative than hydrogen (EN = 2.20). This difference is why water molecules are polar, which is why water dissolves salt, which is why the oceans are salty. The electronegativity trend is the first domino in that causal chain."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Position electronegativity as the bridge concept between COM and STR. COM owns electronegativity as a periodic trend (which atom pulls harder?); STR will import it to determine bond polarity. Provide a short table or partial periodic table with EN values for common elements (H, C, N, O, F, Na, Cl, S, P). Do NOT introduce the Pauling scale derivation or Mulliken alternative. Emphasize the delta-EN concept qualitatively here; the quantitative thresholds (nonpolar/polar/ionic) belong in STR's bond type classification (PRIM-STR001). Foreshadow STR explicitly: "In the next chapter, we will use electronegativity differences to classify bonds."

---

### PRIM-COM007: Valence Electron Reasoning
- **Target section**: COM.2
- **Action**: SYNTHESIZE
- **Canonical source**: OS 6.4--6.5, 7.1, 7.3 (CC-BY 4.0)
- **Supplementary sources**: CLUE 1.2 reasoning framing on valence electrons motivated by bonding prediction (reference only, CC-BY-NC-SA -- do not adapt text; use for pedagogical structure inspiration)
- **Depth**: FULL
- **Reasoning-move framing**: "Given an element's group number on the periodic table, determine its valence electron count and predict its typical bonding behavior (how many bonds it tends to form or how many electrons it tends to gain or lose)."
- **Real-world hook**: "Carbon is in group 14, so it has 4 valence electrons and typically forms 4 bonds. This is why carbon can build the complex molecular scaffolding of life -- from sugars to DNA to plastics."
- **Licensing**: SYNTHESIZE OS-base (OS content provides canonical treatment; CLUE reasoning-first pedagogy informs the motivational structure; all text is original synthesis)
- **Notes**: CLUE motivates valence electrons by asking "why do atoms bond?" before teaching the count -- adopt this motivational ordering (ask the question first, then provide the tool). OS provides the content on electron configurations and group-number shortcuts. SYNTHESIZE these: use CLUE's reasoning-first framing with OS's content. Strip electron configurations beyond valence count (no 1s2 2s2 2p4 notation; just "oxygen has 6 valence electrons because it is in group 16"). Teach only main-group elements. State the octet rule as a predictive heuristic, not a law. Include a simple group-number-to-valence-count table for groups 1, 2, 13--18 with common examples.

---

### PRIM-COM004: Substance Classification
- **Target section**: COM.3
- **Action**: ADAPT
- **Canonical source**: OS 1.2 (CC-BY 4.0)
- **Supplementary sources**: Tro Ch. 3 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a sample description or chemical formula, classify it as an element (one type of atom), compound (two or more types of atoms chemically bonded), or mixture (two or more substances physically combined) to determine what separation or analysis methods are appropriate."
- **Real-world hook**: "Tap water is a mixture (water + dissolved minerals + dissolved gases). Table salt (NaCl) is a compound. The aluminum in a soda can is an element. Knowing which category a sample falls into tells you whether filtering, distilling, or a chemical reaction is needed to separate its components."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: This is a classification/decision-tree skill. Present it as a flowchart: Is the sample pure or mixed? If pure, is it one type of atom or more than one? Use everyday examples exclusively -- avoid lab-only substances. Emphasize that classification is about WHAT is present (composition), not HOW it is arranged (structure). Homogeneous vs. heterogeneous mixtures can be mentioned briefly but should not dominate; the element/compound/mixture triad is the core taxonomy.

---

### PRIM-COM005: Chemical Formula Reading
- **Target section**: COM.3
- **Action**: ADAPT
- **Canonical source**: OS 2.4 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 2 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a chemical formula (molecular, ionic, or empirical), extract which atoms are present, how many of each, and their ratios to determine the quantitative composition of the substance."
- **Real-world hook**: "The ingredient 'sodium bicarbonate (NaHCO3)' on a baking soda box encodes composition: 1 sodium, 1 hydrogen, 1 carbon, 3 oxygen atoms per formula unit. Reading a formula is the gateway to understanding what is in any chemical product."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: This is a literacy/decoding skill. Teach subscript reading, parenthetical groupings (e.g., Ca(OH)2 = 1 Ca, 2 O, 2 H), and coefficient interpretation in the context of balanced equations (preview for CHG domain). Include 5--6 practice formulas of increasing complexity. Do not introduce naming conventions (nomenclature) beyond what is needed to read ingredient labels. Keep the focus on counting atoms from a given formula, not on constructing formulas from names.

---

### PRIM-COM006: Conservation of Atoms
- **Target section**: COM.3
- **Action**: ADAPT
- **Canonical source**: OS 4.1 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 3 (reference only); IUPAC Gold Book, "conservation of mass" (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a before-and-after scenario (a chemical reaction, a physical change, or a claim about matter), verify that atom counts are preserved -- atoms rearrange but are neither created nor destroyed."
- **Real-world hook**: "When wood burns, it seems to disappear. Conservation of atoms says the carbon and hydrogen atoms are still there -- they combined with oxygen to form CO2 and H2O that escaped as gas. The ash is what remains of the non-volatile atoms. Nothing was destroyed; everything was rearranged."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: This is the chemistry-specific conservation law. Present it as a verification tool, not a mathematical exercise. Students should be able to check: "Are the same atoms present before and after?" Introduce equation balancing qualitatively here (the idea that atoms must balance), but defer systematic balancing procedures to the CHG domain. Use the burning-gasoline-to-CO2 example to connect conservation to greenhouse gas reasoning. Flag nuclear reactions as the one exception, but note that nuclear transformations are Enrichment-tier and do not invalidate conservation for all ordinary chemistry.

---

### DEF-COM001: Isotope
- **Target section**: COM.4
- **Action**: ADAPT
- **Canonical source**: OS 2.3 (CC-BY 4.0)
- **Supplementary sources**: IUPAC Gold Book, "isotope" (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given two atoms of the same element (same Z) with different mass numbers, recognize them as isotopes -- same chemical behavior, different mass, potentially different nuclear stability."
- **Real-world hook**: "Carbon-12 and carbon-14 are isotopes. Carbon-14 is radioactive and is used in archaeological dating. The carbon in your food and the carbon-14 used to date ancient artifacts are the same element with the same chemistry -- just different neutron counts."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Emphasize that isotopes have identical chemical behavior because chemistry depends on electrons (which depend on Z), not on neutrons. Mention 2--3 real-world isotope applications: carbon-14 dating, iodine-131 in thyroid treatment, uranium-235 vs. uranium-238 in nuclear fuel. Do NOT teach isotopic notation in depth (no mass-number superscript conventions beyond a brief mention). Do NOT introduce average atomic mass calculations -- defer to SCL if needed. Keep the section short: isotopes are a definition, not a full topic.

---

### DEF-COM002: Ion
- **Target section**: COM.4
- **Action**: ADAPT
- **Canonical source**: OS 2.3, 2.6 (CC-BY 4.0)
- **Supplementary sources**: IUPAC Gold Book, "ion" (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given an atom or group of atoms with a net electric charge (from gaining or losing electrons), recognize it as an ion and predict its charge from periodic position."
- **Real-world hook**: "Sports drinks advertise 'electrolytes' -- these are dissolved ions (Na+, K+, Cl-) that conduct electricity in your body and regulate nerve signals. The periodic table predicts that sodium (group 1) forms Na+ and chlorine (group 17) forms Cl-."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Teach the cation/anion distinction with the periodic position shortcut: group 1 = +1, group 2 = +2, group 16 = -2, group 17 = -1. Introduce polyatomic ions (sulfate, nitrate, carbonate, hydroxide) as a short list to memorize, not derive. Emphasize that ion formation is a composition concept (what charge does this atom carry?) that bridges to structure (how do ions bond? -- handled in STR). Do NOT introduce electron dot diagrams for ion formation here; that belongs in STR's Lewis structure treatment.

---

### PRIM-COM008: Causal Chain Reasoning
- **Target section**: COM.5
- **Action**: WRITE-ORIGINAL
- **Canonical source**: CLUE 1.2, 8.6 (CC-BY-NC-SA) -- reference only; do not adapt text
- **Supplementary sources**: Talanquer 2006, causality dimension (reference only); Bennett et al. 2007 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a chemical claim ('X causes Y'), identify the causal chain: what molecular-level event leads to what macroscopic observation, through what intermediate steps, and whether the claimed causation is supported or merely correlational."
- **Real-world hook**: "A shampoo label claims 'sulfate-free for healthier hair.' Causal chain reasoning asks: what do sulfates do at the molecular level (they are surfactants that strip oils)? Is 'stripping oils' always harmful? For whom? The claim collapses without a complete causal chain from molecular mechanism to health outcome."
- **Licensing**: WRITE-ORIGINAL clean-room (canonical source is CC-BY-NC-SA; all text must be written from scratch to maintain CC-BY 4.0 license)
- **Notes**: This is a meta-reasoning skill with no standalone source section in any CC-BY OER. WRITE-ORIGINAL is required both because of NC-SA licensing on the CLUE source and because no CC-BY source treats causal chain reasoning as a named, explicit skill. Structure the section as: (1) what is a causal chain? (molecular event --> mechanism --> intermediate steps --> macroscopic observation), (2) how do you evaluate one? (is each link supported? is the chain complete? is it correlation or causation?), (3) practice with 2--3 real-world claims (fluoride in water, BPA in plastics, "chemical-free" product labels). This section should be short (1--2 pages) and framed as a thinking tool that students will use throughout the course. Do NOT reproduce any CLUE text or examples.

---

### DEF-COM003: Molecular vs. Empirical Formula (Enrichment)
- **Target section**: COM.E
- **Action**: REWRITE
- **Canonical source**: OS 3.2 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 3 (reference only)
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given composition data for a compound, distinguish between the molecular formula (actual atom count per molecule) and the empirical formula (simplest whole-number ratio of atoms) and determine which one is available from the analytical method used."
- **Real-world hook**: "Formaldehyde (CH2O), acetic acid (C2H4O2), and glucose (C6H12O6) all have the same empirical formula CH2O, but they are vastly different substances. A lab test that gives only the ratio cannot distinguish them."
- **Licensing**: CC-BY 4.0 clean (OS base, rewritten)
- **Notes**: Phase 2 signal is REWRITE. OS treats this at a majors depth with combustion analysis calculations and GCD procedures. REWRITE for non-majors: strip all combustion analysis calculations and empirical-formula-from-percent-composition procedures. Retain only the conceptual distinction (molecular = actual count, empirical = simplest ratio) and the insight that multiple compounds can share the same empirical formula. The n = molar_mass / empirical_formula_mass relationship can be stated conceptually ("you need the molecular weight to tell them apart") without requiring students to calculate it. Mark clearly as Enrichment.

---

### DEF-COM004: Percent Composition (Enrichment)
- **Target section**: COM.E
- **Action**: REWRITE
- **Canonical source**: OS 3.2 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 3 (reference only)
- **Depth**: STRIPPED-QUANTITATIVE
- **Reasoning-move framing**: "Given a chemical formula, calculate the mass fraction (percent by mass) of each element in the compound to connect formula-level composition to mass-level measurements."
- **Real-world hook**: "Comparing calcium supplements: calcium carbonate (CaCO3) is only 40% calcium by mass, while calcium citrate is only 21%. If you need 500 mg of actual calcium, you need a larger pill of calcium citrate."
- **Licensing**: CC-BY 4.0 clean (OS base, rewritten)
- **Notes**: Phase 2 signal is REWRITE. OS presents this as a full quantitative procedure with reverse calculations (percent composition to empirical formula). REWRITE: retain only the forward calculation (formula to percent composition). Allow basic proportional reasoning and multiplication. Strip the reverse direction entirely (empirical formula determination from mass data). Include one worked example (e.g., CaCO3) and one practice problem. Mark clearly as Enrichment. This item depends on DEF-COM003 (also Enrichment), so it must appear after it.

---

## Chapter STR: Structure -- How Does Arrangement Determine Properties?

---

### DEF-STR001: Lewis Structure
- **Target section**: STR.1
- **Action**: ADAPT
- **Canonical source**: OS 7.3 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 4 (reference only); ACS Ch. 3 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a molecular formula and the valence electron count for each atom, distribute electrons as bonding pairs and lone pairs to satisfy the octet rule (duet for H), producing a 2D diagram that shows how atoms are connected and where unshared electrons reside."
- **Real-world hook**: "The Lewis structure of carbon dioxide (O=C=O) shows two double bonds and no lone pairs on carbon, which is why CO2 is linear and nonpolar. Drawing the Lewis structure is the first step to understanding why a chemical behaves the way it does."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Present the Lewis structure algorithm as a step-by-step procedure: (1) count total valence electrons (import from PRIM-COM007), (2) connect atoms with single bonds, (3) distribute remaining electrons as lone pairs to satisfy octets, (4) convert lone pairs to multiple bonds if octets are not satisfied. Include 4--5 worked examples of increasing complexity (H2O, CO2, NH3, CH2O, a polyatomic ion). Mention resonance briefly as "sometimes more than one valid drawing exists" without requiring students to draw all resonance structures. Do NOT introduce formal charge. Do NOT teach exceptions to the octet rule (expanded octets, odd-electron species) -- those are beyond non-majors depth.

---

### PRIM-STR001: Bond Type Classification
- **Target section**: STR.1
- **Action**: ADAPT
- **Canonical source**: OS 7.1, 7.2 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 4 (reference only); Pauling, *The Nature of the Chemical Bond*, Ch. 3 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given two elements and their electronegativities, calculate the electronegativity difference to classify the bond as covalent (shared equally), polar covalent (shared unequally), or ionic (transferred), and predict the resulting material type."
- **Real-world hook**: "Table salt (NaCl) is ionic (delta-EN = 2.1), which is why it forms hard crystals that dissolve in water. Vegetable oil is nonpolar covalent (C-H bonds, delta-EN ~ 0.4), which is why it does not dissolve in water."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Present the delta-EN classification as a practical tool with approximate thresholds (< 0.4 nonpolar, 0.4--1.7 polar covalent, > 1.7 ionic). Emphasize these are guidelines, not rigid cutoffs. Include metallic bonding as a fourth category (metals bonding with metals) but keep treatment brief here -- the full electron sea model is in DEF-STR009 (Enrichment). Use a simple table with 5--6 common bond examples and their delta-EN values. Connect explicitly to DEF-COM005 (electronegativity), which students have already learned in COM.

---

### PRIM-STR002: Bond Polarity Reasoning
- **Target section**: STR.2
- **Action**: ADAPT
- **Canonical source**: OS 7.2 (CC-BY 4.0)
- **Supplementary sources**: Pauling, *The Nature of the Chemical Bond*, Ch. 3 (reference only); Zumdahl Ch. 4 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a bond between two atoms, use their electronegativity difference to determine the direction and magnitude of partial charge separation (which end is delta-negative, which is delta-positive) and predict how that bond contributes to the molecule's overall electron distribution."
- **Real-world hook**: "In a water molecule (H-O-H), oxygen is more electronegative than hydrogen, so each O-H bond has a partial negative charge on the oxygen end. This is why water sticks to glass, climbs up paper towels, and dissolves salt."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Introduce the delta+/delta- notation and the concept of a bond dipole as an arrow pointing from delta+ to delta-. Use 3--4 examples (H-Cl, O-H, C-H, C-O) to build intuition. Emphasize that bond polarity is the molecular-level origin of all electrical asymmetry. This section bridges from periodic-table-level electronegativity (COM) to molecule-level polarity (DEF-STR002, coming later in the chapter). Students must understand individual bond dipoles before they can reason about net molecular dipoles.

---

### PRIM-STR003: Molecular Shape Reasoning
- **Target section**: STR.2
- **Action**: ADAPT
- **Canonical source**: OS 7.6 (CC-BY 4.0)
- **Supplementary sources**: Gillespie & Hargittai, *The VSEPR Model* (reference only); Zumdahl Ch. 5 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a Lewis structure, count the electron groups (bonding pairs and lone pairs) around the central atom, apply electron-pair repulsion (VSEPR model) to predict the 3D molecular geometry, and determine whether the shape produces or cancels molecular polarity."
- **Real-world hook**: "Carbon dioxide (CO2) is linear, so its bond dipoles cancel and it is nonpolar -- that is why CO2 is a gas at room temperature. Water (H2O) is bent, so its bond dipoles do NOT cancel and it is polar -- that is why water is a liquid. Same number of atoms (3), completely different properties, entirely because of shape."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Limit VSEPR shapes to 2, 3, and 4 electron groups only (linear, trigonal planar, bent, tetrahedral, trigonal pyramidal). Do NOT teach 5 or 6 electron-group geometries (trigonal bipyramidal, octahedral) -- these are beyond non-majors depth. Use a clear table mapping (bonding pairs, lone pairs) to molecular geometry and approximate bond angles. Emphasize the distinction between electron geometry (includes lone pairs) and molecular geometry (atoms only) as a common source of student error. Include visual diagrams or suggest 3D model use. Connect shape to polarity: symmetric shapes with identical bonds cancel dipoles; asymmetric shapes or lone pairs produce net dipoles.

---

### DEF-STR002: Molecular Polarity
- **Target section**: STR.2
- **Action**: ADAPT
- **Canonical source**: OS 7.6 (CC-BY 4.0)
- **Supplementary sources**: Pauling, *The Nature of the Chemical Bond*, Ch. 3 (reference only); Zumdahl Ch. 5 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a molecule's shape (from VSEPR) and its bond dipoles (from bond polarity reasoning), determine the vector sum of all bond dipoles to classify the molecule as polar or nonpolar and predict its macroscopic behavior."
- **Real-world hook**: "Why does plastic wrap cling to a glass bowl but not to itself very well? Molecular polarity governs which surfaces stick to which -- it is the reason oil and water separate in salad dressing."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Present molecular polarity as the net result of bond dipoles AND geometry. Use the "tug-of-war" metaphor: if pulls are equal and opposite, they cancel (nonpolar); if pulls are unequal or asymmetric, there is a net pull (polar). Provide a table of 4--5 molecules with their shapes and polar/nonpolar classification (CO2 linear nonpolar, H2O bent polar, CH4 tetrahedral nonpolar, NH3 trigonal pyramidal polar, CCl4 tetrahedral nonpolar). Do NOT require vector arithmetic; qualitative symmetry reasoning is sufficient at non-majors depth. This section completes the bond-polarity-to-molecular-polarity chain and sets up the IMF hierarchy.

---

### DEF-STR003: Hydrogen Bond
- **Target section**: STR.3
- **Action**: ADAPT
- **Canonical source**: OS 10.1 (CC-BY 4.0)
- **Supplementary sources**: Pauling, *The Nature of the Chemical Bond*, Ch. 12 (reference only); Zumdahl Ch. 8 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a molecule containing H bonded to N, O, or F, identify the potential for hydrogen bonding with another molecule's lone pair on N, O, or F, and recognize this as a particularly strong type of dipole-dipole interaction."
- **Real-world hook**: "Why does it take so long to boil a pot of water compared to rubbing alcohol? Water forms extensive hydrogen bond networks (each molecule can form up to 4 hydrogen bonds), requiring much more energy to pull molecules apart into the gas phase."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Present the three criteria clearly: (1) H bonded to N, O, or F in the donor molecule, (2) lone pair on N, O, or F in the acceptor molecule, (3) the interaction is between molecules (intermolecular), not within a molecule. Use a diagram showing the H-bond as a dotted line between molecules. Distinguish hydrogen bonds from covalent bonds explicitly -- this is a major student confusion point (SRC-STR003). Mention that hydrogen bonds are about 10x stronger than ordinary dipole-dipole forces but about 10x weaker than covalent bonds. Connect to water's anomalous properties (high boiling point, ice density) and biological importance (DNA base pairing, protein folding) briefly.

---

### PRIM-STR004: Intermolecular Force Hierarchy
- **Target section**: STR.3
- **Action**: ADAPT
- **Canonical source**: OS 10.1 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 8 (reference only); ACS Ch. 5 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a molecule's structure (polarity, hydrogen-bonding capability, and size), identify which intermolecular forces (IMFs) are present, rank them by strength (London dispersion < dipole-dipole < hydrogen bonding < ionic interactions), and predict relative physical properties."
- **Real-world hook**: "Why does rubbing alcohol evaporate off your skin faster than water? Both are small polar molecules, but water has stronger hydrogen bonds. Stronger IMFs mean harder to vaporize. The IMF hierarchy explains evaporation rate, which is why alcohol feels cold on skin."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Present the hierarchy as a ranking tool with four levels. Emphasize that EVERY molecule has London dispersion forces; polar molecules ADD dipole-dipole; H-bonding molecules ADD hydrogen bonds on top of both. Use a visual ladder or stacking diagram. Stress the intramolecular vs. intermolecular distinction (bonds hold atoms together WITHIN molecules; IMFs hold molecules NEAR each other) -- this is the single most common student confusion in this topic (SRC-STR003). For London forces, explain that larger molecules = more electrons = more polarizable = stronger London forces. Do NOT introduce ion-dipole forces as a separate category; mention them briefly in the context of dissolving ionic compounds.

---

### DEF-STR006: Phase from IMF Balance
- **Target section**: STR.3
- **Action**: ADAPT
- **Canonical source**: OS 10.3 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 8 (reference only); ACS Ch. 5 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a substance's dominant IMF strength and an approximate thermal energy context (room temperature, body temperature, or a stated condition), predict whether the substance is a solid, liquid, or gas by comparing IMF strength to the kinetic energy of the molecules."
- **Real-world hook**: "Methane (CH4) is a gas at room temperature because its only IMFs are weak London forces. Butter is solid in the fridge but liquid in a warm pan because its London forces compete with kinetic energy differently at different temperatures."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Frame phase as a tug-of-war between IMFs (pulling molecules together) and thermal kinetic energy (pushing molecules apart). IMFs win = solid; tie = liquid; kinetic energy wins = gas. Use a simple diagram showing this competition. Do NOT introduce phase diagrams, vapor pressure curves, or Clausius-Clapeyron equation. Keep the treatment qualitative: "stronger IMFs mean higher melting and boiling points." Connect to the IMF hierarchy: students should be able to predict relative boiling points of two substances by comparing their dominant IMFs. Include 2--3 comparison examples (e.g., O2 vs. H2O vs. NaCl).

---

### PRIM-STR005: Structure-to-Property Inference
- **Target section**: STR.4
- **Action**: ADAPT
- **Canonical source**: OS 1.3, 10.2 (CC-BY 4.0)
- **Supplementary sources**: Talanquer threshold schemas, 2015 (reference only); Zumdahl Ch. 8 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a molecule's structural features (polarity, IMF type and strength, shape, and functional groups), predict the direction (higher/lower, more/less) of a macroscopic property -- boiling point, melting point, solubility, viscosity, or vapor pressure -- relative to a comparison molecule."
- **Real-world hook**: "Why is coconut oil solid at room temperature but olive oil is liquid? Both are fats, but coconut oil has more saturated (straight) chains that pack tightly with strong London forces, while olive oil has unsaturated (kinked) chains that pack poorly. Structure-to-property inference: tighter packing = stronger IMFs = solid at room temperature."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: This is the culminating reasoning move of the STR domain. Present it as the capstone skill that chains together everything from bond type through IMFs to macroscopic prediction. Structure the section around 3--4 comparative examples where students must trace the full chain: molecular structure --> polarity --> IMF type --> property prediction. Include boiling point, solubility, and vapor pressure comparisons. Emphasize that predictions are always directional and comparative ("A has a higher bp than B because..."), never numerical. The coconut oil vs. olive oil example is especially effective for non-majors because it connects to everyday cooking experience.

---

### DEF-STR004: "Like Dissolves Like"
- **Target section**: STR.4
- **Action**: ADAPT
- **Canonical source**: OS 11.1, 11.3 (CC-BY 4.0)
- **Supplementary sources**: ACS Ch. 5 (reference only); Zumdahl Ch. 8 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a solute and a solvent, compare their polarities (polar vs. nonpolar) to predict whether the solute will dissolve: polar dissolves in polar, nonpolar dissolves in nonpolar, and polar/nonpolar combinations generally do not mix."
- **Real-world hook**: "Grease stains do not come out with water alone because grease is nonpolar and water is polar. Dish soap works because it has a polar head (dissolves in water) and a nonpolar tail (dissolves in grease), bridging the two."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: Present "like dissolves like" as the single most useful everyday chemistry heuristic. Explain the IMF-compatibility mechanism briefly: a polar solute dissolves when solute-solvent IMFs replace solute-solute IMFs. Use 3--4 everyday examples: salt in water (ionic in polar = dissolves), oil in water (nonpolar in polar = does not dissolve), nail polish in acetone (polar in polar = dissolves), grease in mineral spirits (nonpolar in nonpolar = dissolves). Introduce the concept of soap/detergent as an amphiphilic molecule that bridges polar and nonpolar. Do NOT introduce quantitative solubility rules, Ksp, or solubility product calculations.

---

### DEF-STR010: Water as Solvent
- **Target section**: STR.4
- **Action**: ADAPT
- **Canonical source**: OS 11.1 (CC-BY 4.0)
- **Supplementary sources**: ACS Ch. 5 (reference only); Zumdahl Ch. 8 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given water's molecular structure (bent geometry, high polarity, strong hydrogen bonding capacity), reason about why water is an exceptionally effective solvent for ionic and polar substances, and why it fails to dissolve nonpolar substances."
- **Real-world hook**: "You can dissolve a teaspoon of salt in a glass of water in seconds, but a teaspoon of sand sits unchanged at the bottom. Salt (ionic) is surrounded by water's strong ion-dipole interactions; sand (covalent network solid, nonpolar surface) has no compatible interactions with water."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: This section integrates polarity (DEF-STR002), hydrogen bonding (DEF-STR003), and "like dissolves like" (DEF-STR004) into a single showcase application. Present water's three special structural features: (1) bent geometry = large net dipole, (2) 4 hydrogen bonds per molecule, (3) small size = high density of H-bonding sites. Explain hydration shells around ions with a simple diagram (water molecules orienting O toward cations and H toward anions). Connect to real-world contexts: blood as an aqueous solvent, water pollution (dissolved vs. suspended contaminants), why we drink water and not oil. Do NOT introduce enthalpy of solution, lattice energy calculations, or Born-Haber cycles.

---

### DEF-STR005: Isomer Recognition
- **Target section**: STR.5
- **Action**: ADAPT
- **Canonical source**: OS 20.1 (CC-BY 4.0)
- **Supplementary sources**: ACS Ch. 4 (reference only); Zumdahl Ch. 7 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given two molecules with the same molecular formula, determine whether they are isomers (same formula, different arrangement) by identifying structural differences (different connectivity) or geometric differences (same connectivity, different spatial arrangement), and predict that they will have different properties."
- **Real-world hook**: "Ibuprofen exists as two isomers (R and S forms). Only the S-isomer is the active painkiller; the R-isomer is inactive. Same formula, different arrangement, different biological effect."
- **Licensing**: CC-BY 4.0 clean (OS base, adapted)
- **Notes**: This section directly addresses the additive-to-emergent threshold schema: same atoms, same count, different arrangement = different properties. Limit isomer types to structural (different connectivity) and cis/trans geometric (different spatial arrangement around a double bond). Do NOT introduce chirality, R/S nomenclature, or optical isomerism beyond a brief mention that "mirror-image isomers exist and matter in biology." Use 2--3 pairs of structural isomers with clearly different properties (e.g., ethanol vs. dimethyl ether; butane vs. isobutane). The ibuprofen example effectively motivates why isomers matter for pharmaceutical literacy.

---

### DEF-STR007: Carbon Backbone Reasoning
- **Target section**: STR.5
- **Action**: SYNTHESIZE
- **Canonical source**: OS 20.1--20.4 (CC-BY 4.0)
- **Supplementary sources**: SAY Ch. 15--19 (CC-BY-NC-SA -- reference only for pacing and non-majors depth decisions; do not adapt text); ACS Ch. 4 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given that carbon has 4 valence electrons and forms 4 bonds, reason about how carbon's ability to form stable chains, branches, and rings with other carbon atoms (and with H, O, N, and other elements) produces the enormous diversity of organic molecules."
- **Real-world hook**: "Gasoline (short chains, ~8 carbons) and candle wax (long chains, ~25 carbons) are both hydrocarbons, but the longer chains have stronger London forces and are therefore solid at room temperature. Carbon backbone reasoning explains why organic chemistry produces such an astonishing variety of substances from so few elements."
- **Licensing**: SYNTHESIZE OS-base (OS provides canonical content; SAY informs non-majors pacing decisions; all text is original synthesis)
- **Notes**: Phase 2 signal is ADAPT/REWRITE; select SYNTHESIZE because SAY's 8-chapter non-majors treatment provides valuable pacing guidance that OS (1 chapter at somewhat-majors depth) lacks. Use OS content as the canonical base but adopt SAY's pacing philosophy: spread key ideas across more examples with less depth per example. Focus on three key ideas: (1) carbon's 4-bond versatility, (2) chain length affects London forces and therefore properties, (3) functional groups (OH, COOH, NH2, C=O) create polarity and reactivity. Introduce functional groups as a short recognition table (name, structure, example molecule, polarity effect) -- students should recognize them, not memorize reactions. Do NOT teach IUPAC organic nomenclature beyond the simplest cases (methane, ethanol, acetic acid). Do NOT reproduce any SAY text.

---

### DEF-STR008: Polymer Reasoning
- **Target section**: STR.5
- **Action**: WRITE-ORIGINAL
- **Canonical source**: SAY Ch. 15--19 (CC-BY-NC-SA) -- reference only; do not adapt text
- **Supplementary sources**: OS Ch. 7 (CC-BY 4.0, brief mention only); ACS Ch. 4 (reference only)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a small molecule (monomer), predict how it can link into long repeating chains (polymers), and reason about how polymer chain length, branching, and intermolecular forces determine the material properties of the resulting plastic, fiber, or biological macromolecule."
- **Real-world hook**: "Plastic grocery bags (polyethylene, branched chains, weak London forces) are flexible and melt easily. Kevlar (aromatic polyamide, strong H-bonds between chains) is rigid enough to stop bullets. Both are polymers -- the difference comes entirely from monomer structure and resulting intermolecular forces."
- **Licensing**: WRITE-ORIGINAL clean-room (SAY is the only OER source with adequate non-majors treatment, and it is CC-BY-NC-SA; all text must be written from scratch to maintain CC-BY 4.0 license)
- **Notes**: SAY is the only OER that provides non-majors-appropriate polymer coverage, but its NC-SA license prevents adaptation. WRITE-ORIGINAL from scratch. Structure the section around four structural features that control material properties: (1) chain length (longer = stronger London forces = tougher), (2) branching (more branching = less crystalline = lower density = more flexible), (3) cross-linking (cross-linked = rigid thermoset vs. non-cross-linked = meltable thermoplastic), (4) monomer polarity (polar monomers = stronger IMFs between chains). Include 3--4 everyday polymer examples (polyethylene, PET, nylon, polystyrene) and their structure-property connections. Mention biodegradability briefly (polar groups make polymers more susceptible to hydrolysis). Do NOT reproduce any SAY examples, diagrams, or organizational structure.

---

### DEF-STR009: Metallic Structure (Enrichment)
- **Target section**: STR.E
- **Action**: WRITE-ORIGINAL
- **Canonical source**: CLUE 3.3 (CC-BY-NC-SA) -- reference only; do not adapt text
- **Supplementary sources**: OS Ch. 8 (CC-BY 4.0, brief treatment); Zumdahl Ch. 8 (reference only)
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given a metallic element, reason about the 'electron sea' model -- metal cations arranged in a lattice surrounded by delocalized valence electrons -- to predict metallic properties: electrical conductivity, thermal conductivity, malleability, ductility, and luster."
- **Real-world hook**: "Copper wiring conducts electricity because copper's valence electron is delocalized and free to flow. Gold is hammered into leaf (malleability) because its cation layers slide without breaking the electron sea."
- **Licensing**: WRITE-ORIGINAL clean-room (CLUE canonical source is CC-BY-NC-SA; all text must be written from scratch to maintain CC-BY 4.0 license)
- **Notes**: CLUE provides the most reasoning-aligned treatment of metallic structure, but its NC-SA license requires clean-room writing. WRITE-ORIGINAL from scratch. Keep the section short (1--1.5 pages). Present the electron sea model as a simple picture: metal cations in a grid, valence electrons pooled and mobile. Connect each metallic property to the model: conductivity = free electron flow; malleability = layers slide without directional bond breaking; luster = free electrons absorb/re-emit light. Contrast with ionic solids (which shatter when layers shift, because like charges align). Do NOT introduce band theory, crystal field theory, or detailed lattice structures. Mark clearly as Enrichment. Do NOT reproduce any CLUE text or diagrams.

---

## Summary Statistics

| Metric | Count |
|--------|-------|
| Total items | 28 |
| ADAPT | 20 |
| REWRITE | 3 (PRIM-COM001, DEF-COM003, DEF-COM004) |
| SYNTHESIZE | 2 (PRIM-COM007, DEF-STR007) |
| WRITE-ORIGINAL | 3 (PRIM-COM008, DEF-STR008, DEF-STR009) |
| FULL depth | 24 |
| CONCEPTUAL-ONLY | 2 (DEF-COM003, DEF-STR009) |
| STRIPPED-QUANTITATIVE | 1 (DEF-COM004) |
| Enrichment items | 3 (DEF-COM003, DEF-COM004, DEF-STR009) |
| CC-BY 4.0 clean | 23 |
| WRITE-ORIGINAL clean-room | 3 |
| SYNTHESIZE OS-base | 2 |

---

## NRG Domain Directives (11 items) + SCL Domain Directives (11 items)

---

## Chapter NRG: Energy

### PRIM-NRG001: Energy Tracking
- **Target section**: NRG.1
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 5.1 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 6 Section 6.1
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given a process (chemical reaction, physical change, or energy transfer), trace energy through the system: identify input energy forms, energy transformations within the system, and output energy forms, then verify that total energy is conserved."
- **Real-world hook**: "When you eat a granola bar before a run, chemical energy stored in food bonds is converted to thermal energy (body heat) and mechanical energy (muscle movement). Nothing is lost -- just transformed."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Frame energy tracking as an accounting metaphor -- debits and credits. Present energy forms (chemical, thermal, radiant, electrical, mechanical) with everyday examples. Do NOT introduce calorimetry calculations or q = mc(delta-T). Keep the first law of thermodynamics as a reasoning principle ("the books must balance"), not an equation. Use the granola bar example and build an energy flow diagram as a visual scaffold.

### DEF-NRG001: Heat vs Temperature
- **Target section**: NRG.1
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Sections 5.1, 5.2 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 6 Section 6.1; Granville 1985 (SRC-NRG003, heat/temperature misconceptions)
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given two objects at different temperatures in contact, distinguish heat (the energy transferred between them) from temperature (the average molecular kinetic energy of each), and predict the direction of heat flow (hot to cold) and the eventual equilibrium."
- **Real-world hook**: "A bathtub of lukewarm water contains more total thermal energy than a thimble of boiling water, even though the thimble is at a higher temperature."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: This is the most commonly conflated pair of concepts in introductory chemistry (SRC-NRG003). Lead with the bathtub-vs-thimble comparison. Emphasize: temperature is a property of a single object; heat is a process (transfer). Do NOT introduce the q = mc(delta-T) formula here -- that belongs to DEF-NRG002. Include a simple two-object diagram showing heat flow direction and thermal equilibrium.

### DEF-NRG005: Calorie/Joule
- **Target section**: NRG.1
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 5.1 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 6 Section 6.1
- **Depth**: FULL
- **Reasoning-move framing**: "Given an energy value in calories, kilocalories (food Calories), or joules, convert between units and connect chemistry's energy measurements to everyday nutritional and energy contexts."
- **Real-world hook**: "A nutrition label says a candy bar has 250 Calories. That means burning its molecules releases 250 kcal = 1,046 kJ of energy -- counting Calories IS energy tracking applied to food."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Unit conversion is within the non-majors ceiling. Present the calorie/kilocalorie/food Calorie distinction explicitly (the capital-C confusion is a known stumbling block). Include the carbohydrate ~4 Cal/g, protein ~4 Cal/g, fat ~9 Cal/g approximations as a bridge to nutrition labels. Keep to unit conversion and conceptual mapping; no calorimetry calculations.

### PRIM-NRG002: Bond Energy Reasoning
- **Target section**: NRG.2
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 7.5 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 6 Section 6.4; Bain et al. 2014 (SRC-NRG001, bond energy misconceptions)
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given a chemical reaction, compare the total energy required to break all bonds in the reactants with the total energy released when forming all bonds in the products, then determine whether the reaction is a net energy producer or consumer."
- **Real-world hook**: "Natural gas (methane) burns: breaking C-H and O=O bonds costs energy, but forming C=O and O-H bonds releases MORE energy. The net surplus heats your food."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: This item must directly confront the pervasive misconception that "breaking bonds releases energy." State the correct principle prominently: breaking bonds ALWAYS requires energy input; forming bonds ALWAYS releases energy. Use a qualitative bond-energy comparison diagram (not a table of bond enthalpies for calculation). The methane combustion example should be walked through as "energy in vs. energy out," not as a numerical calculation from a bond-energy table.

### PRIM-NRG003: Exo/Endothermic Classification
- **Target section**: NRG.2
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 5.1 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 6 Section 6.1
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given an energy diagram or description of a process, classify it as exothermic (energy released to surroundings) or endothermic (energy absorbed from surroundings) to predict temperature changes and energy flow direction."
- **Real-world hook**: "Hand warmers (exothermic iron oxidation) make you feel warm; instant cold packs (endothermic ammonium nitrate dissolution) feel cold."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Present as a binary classification. Include a simple energy-level diagram comparing reactants vs. products (E_f < E_i for exothermic, E_f > E_i for endothermic). Emphasize that exo/endo describes direction of energy flow, NOT spontaneity -- that distinction is critical setup for PRIM-NRG005. Do NOT use the delta-H sign convention here; save that for DEF-NRG003.

### DEF-NRG003: Enthalpy Change (delta-H)
- **Target section**: NRG.2
- **Action**: REWRITE
- **Canonical source**: OpenStax *Chemistry 2e* Section 5.3 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 6 Section 6.3; Bain et al. 2014 (SRC-NRG001)
- **Depth**: STRIPPED-QUANTITATIVE
- **Reasoning-move framing**: "Given a chemical reaction occurring at constant pressure, classify the reaction's enthalpy change as negative (exothermic, heat released) or positive (endothermic, heat absorbed) to predict whether the reaction heats or cools its surroundings."
- **Real-world hook**: "Your gas bill: you are paying for the negative delta-H of methane combustion (-890 kJ/mol) that heats your home."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: REWRITE from full Hess's law treatment to conceptual "energy in > energy out = exothermic" reasoning. Strip all Hess's law calculations, standard enthalpy of formation tables, and multi-step enthalpy summation. Retain: the sign convention (negative = exothermic, positive = endothermic), the concept of delta-H as a measurable quantity that lets us compare reactions, and the state function idea (path-independent). Present delta-H as putting a "scoreboard number" on the qualitative exo/endo classification from PRIM-NRG003. Use the gas bill example to ground the kJ/mol unit in everyday experience.

### PRIM-NRG004: Entropy Reasoning
- **Target section**: NRG.3
- **Action**: SYNTHESIZE
- **Canonical source**: OpenStax *Chemistry 2e* Section 16.2 (CC-BY 4.0)
- **Supplementary sources**: CLUE (pedagogical framing: entropy as molecular dispersal/probability, not disorder); Lambert 2002 (SRC-NRG002, why "disorder" is misleading); Zumdahl Ch. 16 Section 16.1
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given a before-and-after description of a process, determine whether the number of possible arrangements (microstates) of energy and matter increased or decreased, and thereby whether the change is entropically favored or disfavored."
- **Real-world hook**: "Why does an ice cube melt on your kitchen counter? Liquid water has enormously more possible arrangements than ice. Melting is overwhelmingly probable -- like shuffling a sorted deck of cards."
- **Licensing**: SYNTHESIZE OS-base (OS CC-BY content base; CLUE framing adapted clean-room for probability/dispersal approach)
- **Notes**: OS Section 16.2 was flagged REWRITE because it leans on the "disorder" metaphor and is overly formal for non-majors. SYNTHESIZE by using OS content as the base but adopting CLUE's pedagogical model: entropy as probability of arrangements (microstates), NEVER as "disorder." Explicitly state that the disorder metaphor is misleading (SRC-NRG002). Use the card-shuffling analogy as the primary scaffold. Provide qualitative predictors: more particles = higher entropy; gas > liquid > solid; higher temperature = higher entropy; larger volume = higher entropy. No Boltzmann equation. No quantitative entropy calculations.

### PRIM-NRG005: Spontaneity Reasoning
- **Target section**: NRG.3
- **Action**: SYNTHESIZE
- **Canonical source**: OpenStax *Chemistry 2e* Section 16.1 (CC-BY 4.0)
- **Supplementary sources**: CLUE (deploys spontaneity from Ch. 5 onward as a recurring reasoning move); Zumdahl Ch. 16 Section 16.4
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given the energy change (exo/endo) AND entropy change (increase/decrease) of a process, determine whether the process will occur without continuous external energy input (spontaneous) or requires sustained external driving (non-spontaneous)."
- **Real-world hook**: "Water freezing at -10 C and ice melting at +25 C are BOTH spontaneous -- temperature determines whether energy or entropy wins."
- **Licensing**: SYNTHESIZE OS-base (OS CC-BY content base; CLUE reasoning-move deployment adapted clean-room)
- **Notes**: OS Section 16.1 is signal ADAPT, but the item benefits from combining OS content with CLUE's pedagogical approach of deploying spontaneity as a recurring reasoning move rather than a late-chapter formalism. Present the four-case grid: (1) exothermic + entropy increase = always spontaneous; (2) endothermic + entropy decrease = never spontaneous; (3) exothermic + entropy decrease = spontaneous at low T; (4) endothermic + entropy increase = spontaneous at high T. Emphasize: spontaneous does NOT mean fast (diamond to graphite is spontaneous but imperceptibly slow). Present the water freezing/melting example as the anchor case for temperature-dependent spontaneity. Do NOT use delta-G = delta-H - T*delta-S; the four-case grid IS the conceptual equivalent.

### PRIM-NRG006: Activation Energy Reasoning
- **Target section**: NRG.4
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 12.5 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 12 Section 12.7
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given a process that is thermodynamically favorable (spontaneous) but does not seem to occur, identify the activation energy barrier that must be overcome to initiate the process, and explain how catalysts or increased temperature can lower or overcome this barrier."
- **Real-world hook**: "Gasoline does not spontaneously combust in your car's fuel tank (activation barrier), but it does when the spark plug fires. A catalytic converter lowers the activation energy for converting toxic exhaust into less harmful products."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Present activation energy as the "hill" in an energy diagram that reactants must climb before rolling down to lower-energy products. Use the match-striking and catalytic converter examples. Clearly distinguish spontaneity (will it happen eventually?) from rate (how fast?). A catalyst provides an alternative pathway with a lower hill, but does NOT change the net energy released/absorbed. Do NOT introduce rate laws, Arrhenius equation, or integrated rate expressions. Keep to the energy-diagram-with-hill visual and qualitative reasoning.

### DEF-NRG002: Specific Heat Capacity
- **Target section**: NRG.4
- **Action**: REWRITE
- **Canonical source**: OpenStax *Chemistry 2e* Section 5.2 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 6 Section 6.2
- **Depth**: STRIPPED-QUANTITATIVE
- **Reasoning-move framing**: "Given two substances receiving the same amount of heat energy, use specific heat capacity to predict which one's temperature will rise more, or given a desired temperature change, determine how much energy is needed."
- **Real-world hook**: "Sand at the beach gets scorching hot by noon, but the ocean stays cool. At night, the sand cools quickly while the water stays warm -- because water has a much higher specific heat capacity."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: REWRITE from OS's calorimetry-calculation focus to a conceptual-comparison focus. Retain the q = mc(delta-T) relationship as a reasoning tool for qualitative comparison (higher c means more energy needed per degree), but strip all calorimetry word problems, bomb calorimeter descriptions, and multi-step calculation exercises. Provide specific heat values for water (4.18 J/g-C) and a contrasting substance like iron (0.449 J/g-C) to anchor the comparison. The beach sand-vs-ocean example is the primary hook. Mention the climate-moderation consequence (coastal vs. inland cities) as a real-world payoff.

### DEF-NRG004: Free Energy (Conceptual)
- **Target section**: NRG.E
- **Action**: REWRITE
- **Canonical source**: OpenStax *Chemistry 2e* Section 16.4 (CC-BY 4.0)
- **Supplementary sources**: CLUE (places free energy early in Ch. 5; good pedagogical model for conceptual treatment); Zumdahl Ch. 16 Section 16.5
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given a process where energy favorability and entropy favorability conflict, evaluate whether the combined effect (free energy) is net favorable (spontaneous) or net unfavorable (non-spontaneous) using qualitative reasoning about relative magnitudes and the role of temperature."
- **Real-world hook**: "Proteins fold into specific shapes spontaneously at body temperature, driven by a combination of enthalpy and entropy. At high fever temperatures, the balance shifts and proteins denature -- which is why fevers above 104 F are dangerous."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: E-tier item. REWRITE from OS's quantitative delta-G = delta-H - T*delta-S treatment to a purely conceptual "nature balances two drives" narrative. Do NOT present the delta-G equation. Instead, present free energy as a conceptual "scorecard" that combines the energy drive and the entropy drive, with temperature as the weighting factor. The four-case grid from PRIM-NRG005 provides the foundation; DEF-NRG004 adds the insight that these cases can be unified under a single concept. The protein folding/denaturation example is the anchor. Mark clearly as Enrichment -- students who master the four-case grid in PRIM-NRG005 have the Core reasoning; free energy is the optional unification.

---

## Chapter SCL: Scale

### PRIM-SCL001: Macro-to-Submicro Translation
- **Target section**: SCL.1
- **Action**: WRITE-ORIGINAL
- **Canonical source**: CLUE Sections 1.5, 5.2 (CC-BY-NC-SA -- cannot reuse)
- **Supplementary sources**: OpenStax *Chemistry 2e* Section 9.1 (CC-BY 4.0); Johnstone 1991 (SRC-GLB003, macro/submicro distinction)
- **Depth**: FULL
- **Reasoning-move framing**: "Given an observable macroscopic property (color, boiling point, solubility, density) or a molecular-level behavior (bond rotation, intermolecular attraction, electron transfer), translate between the two levels -- explaining the macroscopic in terms of the molecular, or predicting the macroscopic from the molecular."
- **Real-world hook**: "A pot of water boils at 100 C. Macro-to-submicro translation asks: what are the water molecules doing? They are gaining enough kinetic energy to overcome hydrogen bonds and escape into the gas phase."
- **Licensing**: WRITE-ORIGINAL clean-room (canonical source is NC-SA; must write from scratch without adapting CLUE text)
- **Notes**: CLUE is the only source with explicit macro-submicro translation as a named reasoning skill, but its NC-SA license prohibits adaptation. Write original content grounded in Johnstone's triplet model (macro, submicro, symbolic). Frame the translation as a bidirectional cognitive operation: top-down (why does X happen? --> molecular explanation) and bottom-up (molecules do Y --> predict macroscopic consequence). Use the boiling water example as the anchor. Do NOT borrow CLUE's specific language, examples, or organizational structure. OS Section 9.1 may be referenced for factual content about gas behavior as supplementary illustration.

### PRIM-SCL004: Emergent Property Reasoning
- **Target section**: SCL.1
- **Action**: WRITE-ORIGINAL
- **Canonical source**: CLUE Section 5.2 "Thinking About Populations" (CC-BY-NC-SA -- cannot reuse)
- **Supplementary sources**: Johnstone 1991 (SRC-GLB003); Talanquer 2015 (SRC-GLB005, threshold schema: emergent properties)
- **Depth**: FULL
- **Reasoning-move framing**: "Given molecular-level features, explain why the bulk (macroscopic) property is NOT a simple sum or average of individual-molecule properties -- the whole behaves differently from any single part."
- **Real-world hook**: "A single gold atom is not shiny and is not yellow. Gold's characteristic color and luster emerge from the collective behavior of trillions of atoms interacting with light through delocalized electrons."
- **Licensing**: WRITE-ORIGINAL clean-room (canonical source is NC-SA; must write from scratch)
- **Notes**: CLUE's "Thinking About Populations" framing is pedagogically strong but NC-SA licensed. Write original content from the Johnstone and Talanquer theoretical foundations. Key examples to develop from scratch: (1) a single water molecule has no melting point -- melting point is a property of 10^23 molecules; (2) gold nanoparticles are red, not gold-colored, because color is scale-dependent. Distinguish emergent properties (boiling point, viscosity, conductivity -- only defined for bulk) from non-emergent properties (molecular mass, bond angle -- definable for one molecule). This item embodies the "centralized to decentralized" threshold schema.

### PRIM-SCL002: Mole Concept
- **Target section**: SCL.2
- **Action**: REWRITE
- **Canonical source**: OpenStax *Chemistry 2e* Section 3.1 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 3; Laugier & Dumon 2004 (SRC-SCL002, mole concept misconceptions)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a number of atoms, molecules, or formula units, convert to moles (divide by 6.02 x 10^23); given moles, convert to mass using molar mass -- thereby bridging the uncountable particle world to the weighable lab world."
- **Real-world hook**: "A recipe calls for '1 cup of sugar.' A chemist's recipe calls for '1 mole of glucose.' Both are counting instructions: 1 mole of glucose (C6H12O6) is 180 g -- the mole lets you 'measure out' the right number of molecules using a balance."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: OS Section 3.1 flagged REWRITE because the treatment is calculation-heavy and front-loads Avogadro's number before establishing why you need it. REWRITE to lead with the conceptual problem: molecules are too small to count individually, so how do chemists "measure out" specific numbers of them? Introduce the mole as chemistry's "dozen" -- a counting word. Then introduce Avogadro's number and molar mass as the tools for converting between particle count, moles, and grams. Use the recipe/cooking analogy as the primary scaffold. Include the conversion chain: particles <--> moles <--> grams as a visual diagram. Do include straightforward unit-conversion examples (non-majors ceiling allows basic algebra and unit conversions).

### PRIM-SCL006: Unit Analysis
- **Target section**: SCL.2
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Sections 1.4, 1.6 (CC-BY 4.0)
- **Supplementary sources**: Arons 1997 (SRC-SCL001, dimensional analysis pedagogy)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a calculation involving physical quantities, use dimensional analysis (tracking units through every step) to verify correctness, convert between unit systems, and catch errors before they propagate."
- **Real-world hook**: "A European recipe calls for 200 mL of milk. Your measuring cup is in cups. Unit analysis: 200 mL x (1 cup / 236.6 mL) = 0.85 cups. The units guide the calculation and verify the answer."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Present unit analysis as a universal error-detection tool: if your answer comes out in the wrong units, something is wrong. Frame it as a problem-solving strategy, not just a checking tool: when stuck, chain conversion factors from starting units to target units. Include one non-chemistry example (recipe conversion) and one chemistry example (grams to moles to molecules). Emphasize that units are algebraic objects that cancel. The medication dosage example (5 mg/kg x 70 kg = 350 mg) is an effective medical-context hook for non-majors.

### PRIM-SCL003: Concentration Reasoning
- **Target section**: SCL.3
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Sections 3.3, 3.4 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 4
- **Depth**: FULL
- **Reasoning-move framing**: "Given a solution, determine the amount of solute per volume of solution (concentration); predict how changing concentration affects rate, biological activity, toxicity, or any concentration-dependent property."
- **Real-world hook**: "A drop of bleach in a swimming pool is harmless; the same bleach undiluted burns skin. The substance is identical -- the concentration is different. 'The dose makes the poison.'"
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Lead with the Paracelsus principle ("the dose makes the poison") to motivate why amount-per-volume matters more than total amount or identity alone. Introduce dilution reasoning (c1V1 = c2V2) qualitatively before naming the formula. Include the water quality report example (lead at 12 ppb vs. EPA action level of 15 ppb) as a real-world reasoning exercise. This section sets up the vocabulary for DEF-SCL001 (molarity) and DEF-SCL002 (ppm/ppb) immediately following.

### DEF-SCL001: Molarity
- **Target section**: SCL.3
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 3.3 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 4
- **Depth**: FULL
- **Reasoning-move framing**: "Given a solution preparation scenario, calculate the number of moles of solute per liter of solution (molarity, M) to express concentration in chemistry's standard unit for reaction stoichiometry and laboratory work."
- **Real-world hook**: "When a municipal water plant adds sodium hypochlorite, engineers calculate molarity to determine how many liters of concentrated stock to dilute into the treatment tank."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Present molarity as the specific, conventional unit that makes concentration reasoning (PRIM-SCL003) precise. Emphasize: M = mol/L is the unit that connects balanced equations (in moles) to volumetric measurements (in liters). Include a simple dilution example using M1V1 = M2V2. The IV drip / pharmacist example is a strong non-majors hook. Keep calculations to straightforward single-step problems (within the non-majors algebra ceiling).

### DEF-SCL002: Parts per Million/Billion (ppm/ppb)
- **Target section**: SCL.3
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 3.4 (CC-BY 4.0)
- **Supplementary sources**: ACS *Chemistry in Context* Ch. 5 (SRC-GLB010)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a trace-level concentration scenario (pollution, contaminants, micronutrients), express concentration in parts per million (mg/L in water) or parts per billion (micrograms/L) to reason about quantities too small for molarity to be intuitive."
- **Real-world hook**: "The EPA's maximum contaminant level for arsenic in drinking water is 10 ppb. A community well tests at 14 ppb -- that exceeds the standard, even though 14 ppb is only 0.014 mg/L, a vanishingly small amount that is nonetheless biologically significant over years of exposure."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Position ppm/ppb as the concentration units for the trace regime -- where molarity values would be inconveniently small (e.g., 0.000014 M). Include the 1 ppm = 1 mg/L (in water) and 1 ppb = 1 microgram/L equivalences. The PFAS detection example (70 ppt in drinking water vs. EPA advisory level) is timely and compelling for non-majors. Emphasize that ppm/ppb is a way of communicating concentration for comparison against regulatory thresholds, not a fundamentally different concept from concentration reasoning.

### PRIM-SCL005: Proportional Reasoning
- **Target section**: SCL.4
- **Action**: REWRITE
- **Canonical source**: OpenStax *Chemistry 2e* Sections 1.6, 4.3 (CC-BY 4.0)
- **Supplementary sources**: Arons 1997 (SRC-SCL001, proportional reasoning pedagogy); Laugier & Dumon 2004 (SRC-SCL002)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a ratio or proportion relating two quantities (molecular ratio from a balanced equation, dilution factor, unit conversion factor), scale it up or down to connect molecular-level ratios to lab-scale quantities."
- **Real-world hook**: "Doubling a cookie recipe: if 2 cups flour serves 24 cookies, 4 cups serves 48 -- the identical reasoning move is used in stoichiometry."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: REWRITE because OS treats proportional reasoning implicitly within stoichiometry problems rather than isolating it as an explicit reasoning skill. Present proportional reasoning as a domain-general cognitive operation first (cooking, medication dosing), then show its chemistry deployment (stoichiometric ratios, dilution). Use a side-by-side comparison: cookie recipe scaling next to mol-ratio scaling. Include the a/b = c/d "solve for the fourth" template. Do NOT include ICE tables or integrated rate law calculations. Keep stoichiometry examples to simple mole-ratio problems from balanced equations.

### DEF-SCL005: Safety and Risk Reasoning
- **Target section**: SCL.4
- **Action**: WRITE-ORIGINAL
- **Canonical source**: SAY Ch. 11 (CC-BY-NC-SA -- cannot reuse)
- **Supplementary sources**: OpenStax *Chemistry 2e* Ch. 18 (environmental chemistry, CC-BY 4.0); ACS *Chemistry in Context* Ch. 1-2 (SRC-GLB010)
- **Depth**: FULL
- **Reasoning-move framing**: "Given a substance with its hazard information (GHS pictograms, LD50, permissible exposure limit, exposure route, and duration), assess the risk to a person by combining the substance's inherent hazard with the concentration, exposure route, and duration of exposure."
- **Real-world hook**: "An SDS for acetone lists LD50 (oral, rat) = 5800 mg/kg and PEL = 1000 ppm. Removing nail polish in a ventilated room is low risk; using acetone in a closed space for hours could approach the PEL. Same substance, different risk."
- **Licensing**: WRITE-ORIGINAL clean-room (canonical source is NC-SA; must write from scratch)
- **Notes**: SAY Ch. 11 (radiation safety) is the canonical source but is NC-SA licensed. Write original content that teaches the hazard vs. risk distinction from first principles. The core reasoning move: Risk = f(Hazard, Concentration, Route, Duration). Hazard is intrinsic (LD50, GHS category); risk is extrinsic (depends on exposure conditions). Include a practical SDS-reading exercise as a worked example. Use the acetone/nail-polish-remover scenario and a cleaning product scenario as anchors. Reference GHS pictograms as visual literacy. Do NOT borrow SAY's text, examples, or organizational structure.

### DEF-SCL003: Ideal Gas Reasoning
- **Target section**: SCL.E
- **Action**: REWRITE
- **Canonical source**: OpenStax *Chemistry 2e* Section 9.2 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 5
- **Depth**: STRIPPED-QUANTITATIVE
- **Reasoning-move framing**: "Given a gas sample, use PV = nRT to relate pressure, volume, temperature, and mole count -- predicting how changing one variable affects the others under the assumption that gas particles do not interact."
- **Real-world hook**: "Why does a basketball go flat in cold weather? Decreasing temperature decreases pressure. Why does a bag of chips puff up on an airplane? Cabin pressure drops while the gas inside stays the same."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: E-tier item. REWRITE from OS's quantitative treatment (multi-step PV = nRT calculations, gas stoichiometry) to qualitative prediction reasoning. Present PV = nRT as a relationship, but emphasize the qualitative predictions: at constant n and T, increasing P decreases V (Boyle); at constant P and n, increasing T increases V (Charles); at constant T and V, increasing n increases P. Use the basketball and chip-bag examples as anchors. Strip all multi-step gas law calculations and combined gas law problems. Retain the conceptual relationship and its predictive power. Mark clearly as Enrichment.

### DEF-SCL004: Colligative Properties
- **Target section**: SCL.E
- **Action**: REWRITE
- **Canonical source**: OpenStax *Chemistry 2e* Section 11.4 (CC-BY 4.0)
- **Supplementary sources**: Zumdahl Ch. 11
- **Depth**: STRIPPED-QUANTITATIVE
- **Reasoning-move framing**: "Given a solution with dissolved particles, predict changes in boiling point, freezing point, vapor pressure, or osmotic pressure based on the NUMBER of dissolved particles, regardless of their chemical identity."
- **Real-world hook**: "Road crews spread salt (NaCl) on icy roads. Each formula unit dissociates into 2 particles (Na+ and Cl-), doubling the freezing-point depression per mole compared to sugar -- that is why salt works better than sugar for de-icing."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: E-tier item. REWRITE from OS's quantitative treatment (delta-Tb = Kb*m*i calculations, osmotic pressure problems) to the conceptual insight: colligative properties depend on particle COUNT, not particle IDENTITY. This is the paradigmatic emergent-scale phenomenon and connects directly to PRIM-SCL004 (emergent property reasoning). Strip all molality-based calculations and colligative property constant tables. Retain: the principle that more dissolved particles = greater effect; the van't Hoff factor i as a qualitative multiplier (NaCl gives 2 particles, CaCl2 gives 3); and the salt-vs-sugar de-icing comparison as the anchor example. Mention boiling-point elevation and freezing-point depression as the two key effects; osmotic pressure may be mentioned briefly but not developed. Mark clearly as Enrichment.

---

## CHG Domain Directives (12 items) + CP Deployment Directives (7 items)

---

## Part A: CHG Item Directives

### PRIM-CHG001: Equation Reading and Balancing
- **Target section**: CHG.1
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 4.1 (CC-BY)
- **Supplementary sources**: Zumdahl *Chemistry* 10e, Section 3.7
- **Depth**: FULL
- **Reasoning-move framing**: "Given a chemical equation with reactants and products, balance it so that atoms of each element are conserved on both sides, and extract the quantitative mole ratios (stoichiometric coefficients) that govern the amounts consumed and produced."
- **Real-world hook**: "A barbecue propane tank label says C3H8. Equation balancing tells you that burning one mole of propane requires five moles of oxygen -- and incomplete combustion in a poorly ventilated grill produces deadly carbon monoxide because there isn't enough O2 to complete the 1:5 ratio."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: OS 4.1 provides solid procedural coverage of balancing by inspection; adapt to non-majors level by foregrounding the *why* (conservation of atoms, PRIM-COM006 callback) before the *how*. Strip stoichiometric calculations beyond simple mole ratios. Retain balanced-equation reading as a qualitative skill: students should be able to read coefficients as mole ratios but are NOT expected to perform mass-to-mass stoichiometry. Include the propane/CO incomplete-combustion hook early to motivate why balancing matters. Ensure PRIM-COM005 (formula reading) and PRIM-COM006 (atom conservation) are explicitly recalled as prerequisite reasoning moves.

---

### PRIM-CHG002: Reaction Type Recognition
- **Target section**: CHG.1
- **Action**: SYNTHESIZE
- **Canonical source**: OpenStax *Chemistry 2e* Section 4.2 (CC-BY)
- **Supplementary sources**: CLUE (CC-BY) -- "field guide" metaphor for reaction classification; Talanquer & Pollard 2010 (SRC-CHG001) -- reaction classification as reasoning patterns
- **Depth**: FULL
- **Reasoning-move framing**: "Given reactants, classify the transformation type -- synthesis, decomposition, single replacement, double replacement, or combustion -- and use the classification to predict the general form of the products."
- **Real-world hook**: "When baking soda meets vinegar, the fizzing tells you a reaction occurred. Reaction type recognition classifies this as a double replacement (acid + carbonate --> salt + water + CO2) -- the same pattern applies to antacid tablets and cleaning limescale."
- **Licensing**: CC-BY 4.0 clean (both OS and CLUE are CC-BY)
- **Notes**: SYNTHESIZE because CLUE's "field guide" metaphor is pedagogically superior to OS's list-based approach; use CLUE's framing of reaction types as a pattern-recognition toolkit (consistent with Talanquer & Pollard's research on teaching reasoning patterns rather than memorized categories). Use OS 4.2 for the formal definitions and examples of each type. Structure the section as a field guide: for each reaction type, present (a) the pattern, (b) how to recognize it from reactants, (c) how to predict products. Emphasize that this is a *reasoning pattern* not a memorization exercise. Recall PRIM-STR001 (bond type classification) to explain why ionic compounds undergo exchange reactions while hydrocarbons undergo combustion.

---

### PRIM-CHG003: Equilibrium Reasoning
- **Target section**: CHG.2
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 13.1 (CC-BY)
- **Supplementary sources**: CLUE Sections 8.5, 9.1 (CC-BY) -- good integration of equilibrium concepts; Zumdahl *Chemistry* 10e, Ch. 13
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given a reversible process, explain why macroscopic properties stabilize even though molecular-level activity continues -- because the forward reaction rate equals the reverse reaction rate -- and predict how the equilibrium position shifts when conditions change."
- **Real-world hook**: "When you open a can of soda, CO2 fizzes out because the equilibrium CO2(dissolved) <=> CO2(gas) was disturbed by the pressure drop. Equilibrium reasoning explains why the soda goes flat faster when warm."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Adapt OS 13.1 but strip ALL quantitative equilibrium treatment: no K expressions, no ICE tables, no Kp/Kc conversions. Retain the conceptual meaning of K (large K = products dominate, small K = reactants dominate, K near 1 = comparable amounts). The critical pedagogical goal is the "static --> dynamic" threshold: equilibrium is NOT a stopped state but a dynamic steady state where forward and reverse rates are equal. Use particle-level animations or diagrams showing molecules continuously reacting in both directions at equal rates. CLUE 8.5/9.1 provide good conceptual integration -- draw on these for the dynamic-balance visualization. Explicitly connect to PRIM-SCL003 (concentration reasoning) as prerequisite. This section sets up DEF-CHG003 (Le Chatelier) in the next subsection.

---

### DEF-CHG003: Le Chatelier's Principle
- **Target section**: CHG.2
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 13.3 (CC-BY)
- **Supplementary sources**: CLUE Section 9.1 (CC-BY); Zumdahl *Chemistry* 10e, Section 13.7
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given a system at equilibrium that is subjected to a stress (change in concentration, temperature, or pressure), predict the direction of the equilibrium shift -- the system partially counteracts the stress by favoring the reaction that reduces it."
- **Real-world hook**: "The Haber process synthesizes ammonia under high pressure and moderate temperature -- conditions chosen using Le Chatelier's principle to maximize yield. The same reasoning explains why hyperventilating makes your blood more basic."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Adapt OS 13.3 (note: coverage matrix lists OS 13.3, which corresponds to Le Chatelier specifically). Strip quantitative Q-vs-K comparisons; retain qualitative shift predictions only. Organize around three stress types: (1) concentration change -- add reactant shifts right, remove product shifts right; (2) temperature change -- treat heat as a reactant (endothermic) or product (exothermic); (3) pressure change -- shifts toward fewer moles of gas. Use the Haber process as the capstone worked example connecting all three stresses. CLUE 9.1 provides good equilibrium-perturbation treatment. Must follow immediately after PRIM-CHG003 since Le Chatelier depends on equilibrium reasoning being in place. Include a common-misconception callout: "Le Chatelier does NOT say the system fully reverses the stress -- it only partially counteracts it."

---

### PRIM-CHG004: Rate Reasoning
- **Target section**: CHG.3
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 12.2 (CC-BY) -- qualitative rate factors (primary)
- **Supplementary sources**: OpenStax *Chemistry 2e* Section 12.1 (CC-BY) -- rate definition (use sparingly, heavily rewrite quantitative parts); Zumdahl *Chemistry* 10e, Ch. 12; Becker et al. 2015 (SRC-CHG002); Cakmakci 2010 (SRC-CHG003)
- **Depth**: STRIPPED-QUANTITATIVE
- **Reasoning-move framing**: "Given conditions such as temperature, concentration, surface area, and presence of a catalyst, predict whether a reaction speeds up or slows down, and explain why in terms of molecular collisions and activation energy."
- **Real-world hook**: "Refrigerating food slows spoilage because lowering temperature reduces the rate of decomposition reactions. Conversely, a pressure cooker speeds cooking by raising temperature. Rate reasoning explains why we refrigerate, why we cook, and why expiration dates exist."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Use OS 12.2 (qualitative rate factors) as the primary source -- it covers temperature, concentration, surface area, and catalyst effects conceptually. From OS 12.1, adapt ONLY the conceptual definition of rate (change in amount over time) and strip ALL rate law equations, rate constants, reaction orders, and integrated rate laws. The central misconception to address (SRC-CHG002, SRC-CHG003): students conflate "favorable" with "fast" -- diamond-to-graphite is spontaneous but imperceptibly slow; dynamite is spontaneous AND fast. Build the section around the four rate factors, each explained via collision theory: (1) temperature -- more kinetic energy, more collisions exceeding Ea; (2) concentration -- more molecules per volume, more collisions; (3) surface area -- more exposed sites; (4) catalyst -- lower Ea. Recall PRIM-NRG006 (activation energy) explicitly. This section sets up DEF-CHG001 (catalyst) immediately after.

---

### DEF-CHG001: Catalyst
- **Target section**: CHG.3
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 12.7 (CC-BY)
- **Supplementary sources**: Zumdahl *Chemistry* 10e, Section 12.7
- **Depth**: FULL
- **Reasoning-move framing**: "Given a reaction that is thermodynamically favorable but too slow, identify a catalyst as a substance that speeds the reaction by providing an alternative pathway with lower activation energy, without being consumed in the process."
- **Real-world hook**: "Your car's catalytic converter uses platinum and palladium to convert toxic exhaust gases (CO, NOx) into less harmful products (CO2, N2, H2O). In your body, the enzyme lactase catalyzes lactose breakdown -- people who are lactose intolerant lack sufficient lactase."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Adapt OS 12.7 directly. Emphasize three key properties: (1) catalyst lowers Ea but does NOT change delta-H or delta-G; (2) catalyst is NOT consumed -- it participates and is regenerated; (3) catalyst does NOT change equilibrium position (K unchanged) -- it only makes equilibrium reached faster. Include an energy diagram showing catalyzed vs. uncatalyzed pathways (same start and end, lower peak). Bridge to enzymes as biological catalysts -- this is the most important catalyst context for non-majors. Address the common misconception that catalysts "make reactions happen" -- they accelerate reactions that are already thermodynamically favorable. No mechanisms (arrow-pushing) per ASM-CHG002.

---

### PRIM-CHG005: Acid-Base Reasoning
- **Target section**: CHG.4
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 14.1 (CC-BY)
- **Supplementary sources**: CLUE Sections 7.2, 9.2, 9.3 (CC-BY) -- good acid-base treatment; Zumdahl *Chemistry* 10e, Ch. 14; ACS *Chemistry in Context* 10e, Ch. 6
- **Depth**: STRIPPED-QUANTITATIVE
- **Reasoning-move framing**: "Given two substances, identify the proton donor (Bronsted acid) and the proton acceptor (Bronsted base), predict the products of the proton transfer, and determine whether the resulting solution is acidic, basic, or neutral."
- **Real-world hook**: "When you take an antacid tablet (CaCO3) for heartburn, acid-base reasoning explains the relief: the carbonate base accepts protons from stomach acid (HCl), neutralizing it. The products are CaCl2, H2O, and CO2 (the burp)."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Adapt OS 14.1 with depth ceiling enforcement. Use Bronsted-Lowry definition exclusively (proton donor/acceptor); do NOT introduce Lewis acid-base theory. Strip Ka/Kb calculations, dissociation constant expressions, and equilibrium calculations for weak acids/bases. Retain: strong vs. weak acid distinction (strong = complete ionization, weak = partial ionization as equilibrium), conjugate acid-base pairs (qualitative), neutralization reaction pattern. CLUE 7.2/9.2/9.3 provide excellent conceptual treatment of proton transfer -- draw on these for the molecular-level visualization of H+ moving from donor to acceptor. Recall PRIM-STR002 (bond polarity) to explain WHY certain molecules release H+ (polar O-H or X-H bonds where X is electronegative). This section leads directly into DEF-CHG002 (pH).

---

### DEF-CHG002: pH Scale
- **Target section**: CHG.4
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 14.2 (CC-BY)
- **Supplementary sources**: Zumdahl *Chemistry* 10e, Section 14.2; CLUE Section 9.2 (CC-BY)
- **Depth**: CONCEPTUAL-ONLY
- **Reasoning-move framing**: "Given a solution, use the pH scale (0-14) to classify it as acidic (pH < 7), neutral (pH = 7), or basic (pH > 7), and relate pH to the concentration of hydrogen ions in solution."
- **Real-world hook**: "A swimming pool should have pH between 7.2 and 7.8. Below 7.2, the water irritates eyes and corrodes fixtures; above 7.8, chlorine becomes less effective. Pool test strips measure pH so you can adjust with acid or base."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Adapt OS 14.2 but present pH conceptually: lower pH = more H+ = more acidic; each unit change = tenfold change in H+ concentration. The logarithmic relationship may be stated (pH = -log[H+]) but students are NOT expected to perform pH calculations. Retain the ability to read the pH scale, place common substances on it (lemon juice ~2, coffee ~5, blood ~7.4, baking soda ~9, ammonia ~11), and interpret the meaning of pH differences. Include a visual pH scale with everyday substances. Recall PRIM-SCL003 (concentration reasoning) to explain that pH is fundamentally about H+ concentration. Must follow immediately after PRIM-CHG005 since it builds on acid-base reasoning.

---

### PRIM-CHG006: Oxidation-Reduction Reasoning
- **Target section**: CHG.5
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 17.1 (CC-BY)
- **Supplementary sources**: CLUE Section 7.5 (CC-BY); SAY *Chemistry* Ch. 20 (metabolism context); Zumdahl *Chemistry* 10e, Ch. 17
- **Depth**: STRIPPED-QUANTITATIVE
- **Reasoning-move framing**: "Given a process, identify electron transfer -- which species loses electrons (is oxidized) and which gains electrons (is reduced) -- and connect the electron flow to practical applications such as batteries, corrosion, and metabolism."
- **Real-world hook**: "A battery converts chemical energy to electrical energy through a controlled redox reaction. In an alkaline AA battery, zinc is oxidized at one terminal and manganese dioxide is reduced at the other. The electrons flow through your flashlight circuit, powering the bulb."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: Adapt OS 17.1 with significant quantitative stripping. Retain: OIL RIG mnemonic, oxidation number rules for identifying electron transfer (element = 0, monatomic ion = charge, O = -2, H = +1), identification of oxidizing and reducing agents. Strip: half-reaction balancing in acidic/basic solution, electrode potential calculations (E-cell), Nernst equation, electrolysis calculations. Present oxidation numbers as a bookkeeping tool for tracking electrons, not as a calculation exercise. CLUE 7.5 provides good conceptual electron-transfer treatment; SAY Ch. 20 contextualizes redox in metabolism (useful for bridging to biology). Recall PRIM-COM007 (valence electron reasoning) as the prerequisite for electron bookkeeping. Focus applications on batteries, corrosion, and biological electron transfer (respiration as controlled oxidation of glucose).

---

### PRIM-CHG007: Nuclear Change Reasoning (E-tier)
- **Target section**: CHG.E
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Sections 21.1, 21.2 (CC-BY)
- **Supplementary sources**: ACS *Chemistry in Context* 10e, Ch. 7 (CC-BY); Zumdahl *Chemistry* 10e, Ch. 20
- **Depth**: STRIPPED-QUANTITATIVE
- **Reasoning-move framing**: "Given an unstable nucleus, predict the type of radiation emitted (alpha, beta, or gamma), write the nuclear equation, and distinguish nuclear change from chemical change by recognizing that different conservation rules apply."
- **Real-world hook**: "Smoke detectors contain americium-241, an alpha emitter. The alpha particles ionize air molecules, creating a current. When smoke enters, it absorbs the alpha particles, the current drops, and the alarm sounds."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: E-tier item; include only in enrichment sections. OS 21.1 needs significant rewrite (strip nuclear stability calculations, binding energy per nucleon curves, belt of stability analysis). OS 21.2 is more adaptable (decay types: alpha, beta, gamma). Use 21.2 as the primary adapted source; from 21.1, retain ONLY the conceptual distinction between chemical change (atoms rearrange, Z preserved) and nuclear change (nucleus transforms, Z changes, element transmutes). Present three decay types with simple nuclear equations showing mass number and atomic number conservation. No nuclear binding energy calculations, no mass defect, no fission/fusion energetics beyond qualitative. Recall DEF-COM001 (isotope) as prerequisite. ACS Ch. 7 provides good non-majors-level nuclear context.

---

### DEF-CHG004: Half-Life (E-tier)
- **Target section**: CHG.E
- **Action**: ADAPT
- **Canonical source**: OpenStax *Chemistry 2e* Section 21.3 (CC-BY)
- **Supplementary sources**: Zumdahl *Chemistry* 10e, Section 20.4; ACS *Chemistry in Context* 10e, Ch. 7
- **Depth**: STRIPPED-QUANTITATIVE
- **Reasoning-move framing**: "Given a radioactive isotope, use its half-life (the time for half of a sample to decay) to predict how much remains after a given number of half-lives, and apply this to dating, medical diagnostics, and nuclear waste management."
- **Real-world hook**: "Carbon dating works because living organisms maintain a constant C-14/C-12 ratio; after death, C-14 decays with a 5,730-year half-life. Measuring the remaining fraction tells archaeologists the age."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: E-tier item; depends on PRIM-CHG007 (also E-tier), so include only in enrichment sections. Adapt OS 21.3 with depth ceiling: retain the (1/2)^n pattern for whole-number half-lives only. Students should be able to calculate: after 1 half-life, 50% remains; after 2, 25%; after 3, 12.5%. Strip: exponential decay equations, first-order kinetics derivations, logarithmic age calculations. Present half-life as constant and independent of temperature/pressure/chemistry (contrast with chemical reaction rates). Applications: C-14 dating (archaeology), I-131 clearance (nuclear medicine, 8-day half-life), U-238 dating (geology, 4.5 billion years). Include a simple table or diagram showing successive halvings.

---

### DEF-CHG005: Precipitation (E-tier)
- **Target section**: CHG.E
- **Action**: REWRITE
- **Canonical source**: OpenStax *Chemistry 2e* Section 15.1 (CC-BY)
- **Supplementary sources**: None (single-source item; most expendable E-tier item)
- **Depth**: STRIPPED-QUANTITATIVE
- **Reasoning-move framing**: "Given two aqueous ionic solutions mixed together, determine whether an insoluble ionic product (precipitate) forms by checking solubility rules, and predict the identity of the solid that crashes out of solution."
- **Real-world hook**: "Hard water contains dissolved Ca2+ and Mg2+ ions. When heated, calcium reacts with bicarbonate to precipitate CaCO3 -- the white scale inside your kettle. Water softeners replace Ca2+ with Na+, which does not form insoluble precipitates."
- **Licensing**: CC-BY 4.0 clean
- **Notes**: E-tier item and the most expendable entry in the CHG domain. REWRITE because OS 15.1 focuses on Ksp (solubility product) calculations, which are entirely above the non-majors depth ceiling. Rewrite from scratch using only qualitative solubility rules: most Na+/K+/NH4+ salts soluble; most NO3- salts soluble; most Cl- soluble except Ag+, Pb2+, Hg2+; most SO4^2- soluble except Ba2+, Pb2+. Strip: Ksp expressions, molar solubility calculations, common-ion effect quantitative treatment. Frame as a specific case of double-replacement reaction (callback to PRIM-CHG002): ions swap partners, and if one combination is insoluble, it precipitates. Include solubility rules as a reference table, not a memorization requirement. Use the hard-water/kettle-scale hook and water-treatment context. This item can be omitted entirely if time is constrained without breaking any dependency chain.

---

## Part B: Composition Pattern Deployment Directives

### CP-001: Structure-to-Property Prediction (Deployment)
- **Target section**: SCL.CP-001, end of Ch 4
- **Action**: DEPLOY-CP
- **ADP template**: ADP-001
- **Prerequisite domains**: STR (Ch 2), SCL (Ch 4)
- **Key items deployed**: PRIM-STR004 (IMF hierarchy), PRIM-STR005 (structure-to-property inference), PRIM-SCL001 (macro-to-submicro translation), PRIM-SCL004 (emergent property reasoning)
- **Real-world hook**: "Why does rubbing alcohol evaporate faster than water?"
- **Bridge question**: "Why don't oil and water mix?"
- **Notes**: Follow ADP-001 four-step sequence exactly. Step 1: explicitly name all four primitives as reusable reasoning tools. Step 2: present the rubbing-alcohol evaporation hook as a concrete puzzle. Step 3: walk through the reasoning chain -- classify IMFs in each liquid (PRIM-STR004), infer property consequence (PRIM-STR005), translate from molecular to macroscopic (PRIM-SCL001), recognize emergence (PRIM-SCL004). Step 4: bridge to oil-and-water immiscibility using the identical four-step chain. The bridge is the key pedagogical move -- it proves the reasoning is transferable, not just memorized for one example. Placement at end of Ch 4 ensures both STR and SCL primitives are in place.

---

### CP-004: Greenhouse Effect (Deployment)
- **Target section**: SCL.CP-004, end of Ch 4
- **Action**: DEPLOY-CP
- **ADP template**: ADP-004
- **Prerequisite domains**: STR (Ch 2), NRG (Ch 3), SCL (Ch 4)
- **Key items deployed**: PRIM-STR003 (molecular shape reasoning), PRIM-STR002 (bond polarity reasoning), PRIM-NRG002 (bond energy reasoning), PRIM-SCL004 (emergent property reasoning)
- **Real-world hook**: "Why is CO2 a greenhouse gas but N2 is not?"
- **Bridge question**: "Why is methane worse than CO2 for climate?"
- **Notes**: Follow ADP-004 four-step sequence. This is the most socially relevant CP for non-majors: climate change is the defining scientific issue for this audience. The reasoning chain must be presented as chemistry, not politics: bond polarity determines whether dipole changes are possible (PRIM-STR002), molecular shape determines which vibrations are IR-active (PRIM-STR003), energy reasoning explains absorption (PRIM-NRG002), and emergence scales molecular absorption to planetary warming (PRIM-SCL004). The methane bridge is especially powerful because it introduces the concept of per-molecule potency (methane is ~80x worse than CO2 over 20 years) using the same four primitives. Ensure that "dipole change during vibration" is explained qualitatively, not mathematically. Placement at end of Ch 4 alongside CP-001; both serve as STR+SCL capstones (CP-004 adds NRG).

---

### CP-002: Energy-Driven Transformation (Deployment)
- **Target section**: CHG.CP-002, end of Ch 5
- **Action**: DEPLOY-CP
- **ADP template**: ADP-002
- **Prerequisite domains**: NRG (Ch 3), CHG (Ch 5)
- **Key items deployed**: PRIM-NRG005 (spontaneity reasoning), PRIM-NRG003 (exo/endothermic classification), PRIM-CHG003 (equilibrium reasoning), PRIM-CHG006 (oxidation-reduction reasoning)
- **Real-world hook**: "Why does a battery eventually die?"
- **Bridge question**: "Why does ice melt at room temperature?"
- **Notes**: Follow ADP-002 four-step sequence. This CP is the NRG-CHG interface capstone and directly addresses the most persistent misconception in CHG: conflating "favorable" (NRG) with "fast" (CHG). The battery hook is ideal because it involves all four primitives naturally -- redox identifies the electron flow, spontaneity explains why it happens, exo/endo classifies the energy flow, and equilibrium explains why it stops. The ice-melting bridge is intentionally simple (a phase change, not a redox reaction) to show that the NRG-CHG reasoning applies broadly. Emphasize that equilibrium is the general explanation for "why processes stop" -- batteries die when the redox system reaches equilibrium. Do NOT include cell-potential calculations or Nernst equation.

---

### CP-003: Acid-Base in the Body (Deployment)
- **Target section**: CHG.CP-003, end of Ch 5
- **Action**: DEPLOY-CP
- **ADP template**: ADP-003
- **Prerequisite domains**: STR (Ch 2), CHG (Ch 5), SCL (Ch 4)
- **Key items deployed**: PRIM-STR002 (bond polarity reasoning), PRIM-STR005 (structure-to-property inference), PRIM-CHG005 (acid-base reasoning), DEF-CHG002 (pH scale), PRIM-SCL003 (concentration reasoning)
- **Real-world hook**: "Why does aspirin hurt your stomach but an antacid helps?"
- **Bridge question**: "Why does lemon juice taste sour but soap feels slippery?"
- **Notes**: Follow ADP-003 five-primitive sequence. This is the most personally relevant CP for non-majors -- it connects to digestion, medication, food, and cleaning. The aspirin hook requires all five primitives: bond polarity identifies the acid functional group, structure-to-property explains why it donates H+, acid-base reasoning traces the proton transfer, pH quantifies the acidity change, and concentration reasoning explains dose-dependence. The antacid reversal (same primitives, opposite direction) is a powerful "aha" moment. The lemon/soap bridge transfers the same chain to taste and touch. Phase 4 writers should ensure that carboxylic acid groups (-COOH) are presented structurally (molecular diagram) so students can SEE the polar O-H bond, not just be told about it.

---

### CP-005: Dose Makes the Poison (Deployment)
- **Target section**: CHG.CP-005, end of Ch 5
- **Action**: DEPLOY-CP
- **ADP template**: ADP-005
- **Prerequisite domains**: STR (Ch 2), CHG (Ch 5), SCL (Ch 4)
- **Key items deployed**: PRIM-STR005 (structure-to-property inference), PRIM-CHG005 (acid-base reasoning), PRIM-CHG006 (redox reasoning), PRIM-SCL003 (concentration reasoning), DEF-SCL002 (parts per million/billion)
- **Real-world hook**: "Is fluoride in drinking water safe?"
- **Bridge question**: "Is chlorine in pool water dangerous?"
- **Notes**: Follow ADP-005 four-step sequence. This CP is the scientific-literacy capstone: it provides the intellectual toolkit to evaluate chemical safety claims rationally, combating the binary "safe vs. dangerous" thinking that characterizes chemical illiteracy. The fluoride hook deploys acid-base reasoning (enamel protection via acid resistance); the chlorine bridge deploys redox reasoning (oxidizing agent that kills pathogens). Both converge on the same conclusion: concentration is the deciding variable, not molecular identity. Phase 4 writers should explicitly connect to public discourse: "When you read a headline claiming a chemical is 'toxic,' the first question a chemist asks is: at what concentration?" Include EPA guideline numbers (0.7 ppm fluoride, 1-3 ppm chlorine) to ground the reasoning quantitatively via DEF-SCL002.

---

### CP-006: Food Chemistry (Deployment)
- **Target section**: CHG.CP-006, end of Ch 5
- **Action**: DEPLOY-CP
- **ADP template**: ADP-006
- **Prerequisite domains**: COM (Ch 1), NRG (Ch 3), CHG (Ch 5), SCL (Ch 4)
- **Key items deployed**: PRIM-COM006 (conservation of atoms), PRIM-NRG002 (bond energy reasoning), PRIM-NRG003 (exo/endothermic classification), PRIM-CHG004 (rate reasoning), PRIM-SCL002 (mole concept / amount reasoning)
- **Real-world hook**: "Why do we cook food?"
- **Bridge question**: "Why do food labels list Calories?"
- **Notes**: Follow ADP-006 five-primitive sequence. This is the most domain-rich CP (4 domains) and demonstrates that even the most familiar everyday activity -- eating -- involves cross-domain chemistry. The cooking hook walks through: heat increases reaction rate (PRIM-CHG004), bond energy is released during metabolism (PRIM-NRG002), metabolism is exothermic (PRIM-NRG003), atoms are conserved through every transformation (PRIM-COM006), and Calories quantify the macroscopic energy content (PRIM-SCL002). The food-label bridge is the critical transfer: a Calorie count is a macroscopic summary of molecular bond energy. Phase 4 writers should consider a visual showing a slice of bread --> metabolic products (CO2 + H2O) with atom-tracking arrows and energy accounting. Do NOT introduce detailed metabolic pathways (glycolysis, etc.) -- keep at the "food in, CO2 + H2O + energy out" level.

---

### CP-007: Biochemistry Connection (Deployment)
- **Target section**: CH6.CP-007, Ch 6 standalone
- **Action**: DEPLOY-CP
- **ADP template**: ADP-007
- **Prerequisite domains**: STR (Ch 2), CHG (Ch 5), SCL (Ch 4)
- **Key items deployed**: PRIM-STR004 (IMF hierarchy), PRIM-STR005 (structure-to-property inference), DEF-STR007 (carbon backbone reasoning), DEF-STR008 (polymer reasoning), PRIM-CHG004 (rate reasoning), PRIM-SCL004 (emergent property reasoning)
- **Real-world hook**: "Why does DNA have a double helix?"
- **Bridge question**: "Why do proteins fold into specific shapes?"
- **Notes**: Follow ADP-007 six-primitive sequence. E-tier CP serving as the course capstone in Ch 6. This pattern demonstrates the ultimate transferability of chemical reasoning: the same primitives that explain why rubbing alcohol evaporates (IMFs, structure-to-property, emergence) also explain why DNA stores information and why proteins catalyze reactions. The DNA hook walks from polymer structure (DEF-STR008) through carbon backbone (DEF-STR007), hydrogen bonding between base pairs (PRIM-STR004), structure-determines-function (PRIM-STR005), to emergence of information storage from 3 billion ordered base pairs (PRIM-SCL004). The protein bridge adds enzyme catalysis via rate reasoning (PRIM-CHG004). Phase 4 writers should include simplified structural diagrams of DNA base pairing (showing H-bonds explicitly) and a protein folding schematic. No amino acid memorization, no genetic code details, no enzyme kinetics -- the goal is to show that biological molecules obey the same chemical principles, not to teach biochemistry.

---

## Verification Summary

### Item Count Verification

| Domain | Expected | Directives Written | Match? |
|--------|----------|-------------------|--------|
| COM | 13 | 13 | ✓ |
| STR | 15 | 15 | ✓ |
| NRG | 11 | 11 | ✓ |
| SCL | 11 | 11 | ✓ |
| CHG | 12 | 12 | ✓ |
| **Total items** | **62** | **62** | **✓** |
| CPs | 7 | 7 | ✓ |
| **Grand total** | **69** | **69** | **✓** |

### WRITE-ORIGINAL Items (Clean-Room Protocol Required)

| Item | Domain | Reason |
|------|--------|--------|
| PRIM-COM008 | COM | META status — no standalone source section in any CC-BY source |
| DEF-STR008 | STR | Canonical source (SAY) is CC-BY-NC-SA |
| DEF-STR009 | STR | Canonical source (CLUE) is CC-BY-NC-SA |
| PRIM-SCL001 | SCL | Canonical source (CLUE) is CC-BY-NC-SA |
| PRIM-SCL004 | SCL | Canonical source (CLUE) is CC-BY-NC-SA |
| DEF-SCL005 | SCL | Canonical source (SAY) is CC-BY-NC-SA |

6 items total: 1 META + 5 NC-SA canonical.

**Note**: Phase 4 writers MUST NOT read the NC-SA source text during writing of these items. Use only the taxonomy item spec (DOMAIN-{CODE}.md), general chemistry knowledge, and CC-BY sources (OS) for background context.

### E-Tier Items

All 8 E-tier items + 1 E-tier CP have directives and are marked as Enrichment:
DEF-COM003, DEF-COM004, DEF-STR009, DEF-NRG004, DEF-SCL003, DEF-SCL004, PRIM-CHG007, DEF-CHG005, CP-007.

DEF-CHG004 (half-life) is listed Core in registry but depends on E-tier PRIM-CHG007; effectively E-tier in the architecture.
