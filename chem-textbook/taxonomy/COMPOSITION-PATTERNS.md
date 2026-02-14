# COMPOSITION-PATTERNS v0.1

Cross-domain composition patterns for the chemistry taxonomy. Each pattern documents a reasoning chain that **genuinely requires** primitives from two or more domains -- removing any domain breaks the reasoning. Full specifications follow the template in CONVENTIONS.md Section 11.

**Total**: 7 patterns (6 Core + 1 Enrichment)

**Governing constraint**: Every pattern listed here MUST be irreducibly cross-domain. If the reasoning chain can be completed using a single domain's primitives, it is not a composition pattern but an intra-domain result and MUST be moved to the relevant domain spec.

---

## CP-001: **Structure-to-Property Prediction**

- **Domains**: STR x SCL
- **Statement**: Given a molecular structure, predict a bulk (macroscopic) physical property by reasoning through intermolecular forces and scale bridging.
- **Natural language**: Molecular-level features (bond polarity, molecular shape, IMF type) determine how strongly molecules attract each other. The collective effect of billions of these molecular interactions produces observable bulk properties like boiling point, evaporation rate, and solubility. STR provides the molecular reasoning; SCL bridges from the single-molecule picture to the macroscopic observation.
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| STR | PRIM-STR004 (IMF hierarchy), PRIM-STR005 (structure-to-property inference) |
| SCL | PRIM-SCL001 (macro-to-submicro translation), PRIM-SCL004 (emergent property reasoning) |

- **Real-world hook**: "Why does rubbing alcohol evaporate faster than water?"
- **Reasoning chain**:
  1. **PRIM-STR004** (IMF hierarchy): Classify the dominant intermolecular forces in each liquid. Water has extensive hydrogen bonding (strong IMFs). Isopropanol has fewer H-bonds and more London dispersion forces (weaker net IMFs).
  2. **PRIM-STR005** (structure-to-property): Infer that weaker IMFs mean molecules escape the liquid phase more easily, requiring less energy to vaporize.
  3. **PRIM-SCL001** (macro-to-submicro): Translate the molecular-level conclusion (easier escape) to the macroscopic observation (faster evaporation, lower boiling point).
  4. **PRIM-SCL004** (emergence): Recognize that the bulk evaporation rate is an emergent property arising from the collective behavior of billions of molecules, each governed by the same IMF balance.
- **Bridging application**: "Why don't oil and water mix?" -- Same primitives: water is polar with extensive H-bonding (PRIM-STR004); oil is nonpolar with only London dispersion forces. Mixing would require disrupting water's H-bonding network without comparable replacement interactions (PRIM-STR005). The macroscopic phase separation (PRIM-SCL001) emerges from molecular-level incompatibility (PRIM-SCL004).
- **Tier**: C
- **Significance**: This is arguably the single most important cross-domain pattern for non-majors. It answers the question "why does this substance behave this way?" by connecting invisible molecular features to tangible everyday observations. Without STR, we cannot explain *why* a property exists. Without SCL, we cannot bridge from one molecule to a beaker of liquid.

---

## CP-002: **Energy-Driven Transformation**

- **Domains**: NRG x CHG
- **Statement**: Given a chemical system undergoing change, predict whether and how far the reaction proceeds by combining energy reasoning (spontaneity, exo/endo) with transformation reasoning (equilibrium, redox).
- **Natural language**: Whether a reaction "wants" to happen is determined by energy considerations (enthalpy, entropy, free energy). How the reaction actually unfolds -- what gets oxidized or reduced, where equilibrium lies, whether the reaction goes to completion -- is governed by transformation logic. NRG provides the thermodynamic driving force; CHG provides the mechanistic and equilibrium framework.
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| NRG | PRIM-NRG005 (spontaneity reasoning), PRIM-NRG003 (exo/endothermic classification) |
| CHG | PRIM-CHG003 (equilibrium reasoning), PRIM-CHG006 (oxidation-reduction reasoning) |

- **Real-world hook**: "Why does a battery eventually die?"
- **Reasoning chain**:
  1. **PRIM-CHG006** (redox reasoning): Identify the battery as running a spontaneous redox reaction -- one electrode is oxidized, the other's ions are reduced, and electrons flow through the circuit as usable electricity.
  2. **PRIM-NRG005** (spontaneity): The reaction proceeds because it is thermodynamically favorable (negative free energy change). The system moves toward lower energy.
  3. **PRIM-NRG003** (exo/endo): The overall process is exothermic -- chemical potential energy is converted to electrical energy and heat.
  4. **PRIM-CHG003** (equilibrium): As reactants are consumed and products accumulate, the system approaches equilibrium. At equilibrium, the forward and reverse reaction rates are equal and no net driving force remains -- the battery is "dead."
- **Bridging application**: "Why does ice melt at room temperature?" -- Same spontaneity reasoning (PRIM-NRG005): the entropy gain from disordering the rigid ice lattice outweighs the enthalpy cost of breaking hydrogen bonds at temperatures above 0 degrees C. The system spontaneously transforms (PRIM-CHG003 in the trivial limit: the equilibrium strongly favors liquid water at room temperature). The energy flow is endothermic (PRIM-NRG003) -- heat flows from surroundings into the ice.
- **Tier**: C
- **Significance**: This pattern underlies every "will it react?" and "how far will it go?" question in chemistry. Without NRG, we cannot explain *why* the reaction proceeds. Without CHG, we cannot describe *what* is actually happening at the molecular level or predict *where* the system ends up. Non-majors encounter this pattern in batteries, cooking, corrosion, and biological metabolism.

---

## CP-003: **Acid-Base in the Body**

- **Domains**: STR x CHG x SCL
- **Statement**: Given an acid or base interacting with a biological or everyday system, predict the chemical outcome by reasoning through molecular structure (what makes it an acid or base), transformation logic (the proton-transfer reaction), and scale (concentration determines severity).
- **Natural language**: Whether a substance acts as an acid or base depends on its molecular structure -- specifically, which bonds can donate or accept protons. The acid-base reaction itself is a chemical change governed by proton-transfer equilibria. But the *effect* of that reaction (soothing vs. harmful, mild vs. severe) depends on concentration and dose at the macroscopic scale. All three domains are needed: structure explains *what kind* of acid/base, change explains *what happens*, and scale explains *how much matters*.
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| STR | PRIM-STR002 (bond polarity reasoning), PRIM-STR005 (structure-to-property inference) |
| CHG | PRIM-CHG005 (acid-base reasoning), DEF-CHG002 (pH scale) |
| SCL | PRIM-SCL003 (concentration reasoning) |

- **Real-world hook**: "Why does aspirin hurt your stomach but an antacid helps?"
- **Reasoning chain**:
  1. **PRIM-STR002** (bond polarity) + **PRIM-STR005** (structure-to-property): Aspirin (acetylsalicylic acid) contains a carboxylic acid group with a polar O-H bond. This structural feature makes it capable of donating H+ ions. Molecular structure determines acid behavior.
  2. **PRIM-CHG005** (acid-base reasoning): In the acidic environment of the stomach, aspirin donates H+ ions, further lowering the local pH. This excess acidity irritates the stomach lining.
  3. **DEF-CHG002** (pH scale): The pH quantifies the severity -- aspirin shifts the stomach environment to a lower pH value, meaning higher acidity.
  4. **PRIM-SCL003** (concentration reasoning): The *degree* of irritation depends on concentration. One aspirin tablet produces a manageable local pH drop; a handful overwhelms the stomach's buffering capacity.
  5. **PRIM-CHG005** (acid-base, reverse direction): An antacid like Mg(OH)2 accepts H+ ions (acts as a base), neutralizing the excess acid and raising the pH back toward normal. Same acid-base reasoning, opposite direction.
- **Bridging application**: "Why does lemon juice taste sour but soap feels slippery?" -- Lemon juice contains citric acid, whose structure (PRIM-STR005) features multiple carboxylic acid groups that donate H+ (PRIM-CHG005), producing a low pH (DEF-CHG002) detected by taste receptors. Soap contains sodium hydroxide residues that accept H+ (base), producing a high pH. The intensity of sourness or slipperiness depends on concentration (PRIM-SCL003).
- **Tier**: C
- **Significance**: Acid-base chemistry is the most personally relevant chemistry topic for non-majors -- it connects to digestion, medication, food, cleaning products, and environmental issues like ocean acidification. This three-domain pattern shows that understanding requires structure (what makes it acidic), change (the proton-transfer reaction), and scale (dose/concentration determines outcome). Removing any domain leaves an incomplete explanation.

---

## CP-004: **Greenhouse Effect**

- **Domains**: STR x NRG x SCL
- **Statement**: Given a gas in the atmosphere, predict whether it acts as a greenhouse gas by reasoning through molecular structure (shape and bond polarity), energy absorption (IR interaction with bonds), and scale (collective atmospheric effect).
- **Natural language**: Whether a molecule absorbs infrared radiation depends on its structure: it must have bonds whose vibrations produce a changing dipole moment. The energy reasoning explains *what happens* when IR photons meet those bonds (absorption and re-emission). But the climate-level consequence requires scale reasoning: individual molecular absorptions, multiplied across billions of molecules at specific atmospheric concentrations, produce the emergent phenomenon of global warming.
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| STR | PRIM-STR003 (molecular shape reasoning), PRIM-STR002 (bond polarity reasoning) |
| NRG | PRIM-NRG002 (bond energy reasoning / absorption) |
| SCL | PRIM-SCL004 (emergent property reasoning) |

- **Real-world hook**: "Why is CO2 a greenhouse gas but N2 is not?"
- **Reasoning chain**:
  1. **PRIM-STR002** (bond polarity): CO2 has polar C=O bonds (oxygen is more electronegative than carbon). N2 has a nonpolar N-N bond (identical atoms, no electronegativity difference).
  2. **PRIM-STR003** (molecular shape): CO2 is linear and symmetric overall, but its asymmetric stretching vibration creates a transient dipole moment change. N2 is symmetric with no possible dipole change during vibration.
  3. **PRIM-NRG002** (bond energy / absorption): When infrared radiation matches the vibrational frequency of CO2's asymmetric stretch, the molecule absorbs the photon's energy. N2 cannot absorb IR because its vibrations produce no dipole change -- it is transparent to infrared.
  4. **PRIM-SCL004** (emergence): One CO2 molecule absorbing one IR photon is insignificant. But 420+ ppm of CO2 in the atmosphere means billions of molecules collectively trapping and re-emitting thermal radiation, producing the emergent macroscopic effect of atmospheric warming.
- **Bridging application**: "Why is methane worse than CO2 for climate?" -- Methane (CH4) has polar C-H bonds (PRIM-STR002) and a tetrahedral shape (PRIM-STR003) with multiple IR-active vibrational modes, allowing it to absorb infrared radiation across more wavelengths (PRIM-NRG002). Per molecule, methane absorbs more effectively than CO2, so even at lower atmospheric concentrations, its collective warming effect (PRIM-SCL004) is roughly 80 times greater per molecule over 20 years.
- **Tier**: C
- **Significance**: Climate change is the defining scientific issue for today's non-majors. This pattern demonstrates that understanding the greenhouse effect is not a matter of political opinion but of molecular reasoning: structure determines IR absorption, energy explains the mechanism, and scale connects molecular events to planetary consequences. Removing STR leaves no explanation for *why* CO2 absorbs IR. Removing NRG leaves no mechanism for the absorption. Removing SCL leaves no bridge from one molecule to a warming planet.

---

## CP-005: **Dose Makes the Poison**

- **Domains**: STR x CHG x SCL
- **Statement**: Given a chemical substance and a dose, predict whether the exposure is beneficial, neutral, or harmful by reasoning through molecular structure (what the substance does chemically), the relevant chemical change (how it interacts with biological systems), and concentration/dose at the macroscopic scale.
- **Natural language**: The same molecule can be a medicine at one dose and a toxin at another. Structure determines *what* the molecule can do (its chemical reactivity and biological interactions). Change reasoning identifies *how* it reacts in the body (acid-base neutralization, redox reactions, enzyme interactions). But the outcome -- helpful or harmful -- is determined by scale: concentration and dose govern whether the chemical change is therapeutic or destructive. This pattern operationalizes the toxicological principle attributed to Paracelsus: "the dose makes the poison."
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| STR | PRIM-STR005 (structure-to-property inference) |
| CHG | PRIM-CHG005 (acid-base reasoning) or PRIM-CHG006 (redox reasoning) |
| SCL | PRIM-SCL003 (concentration reasoning), DEF-SCL002 (parts per million/billion) |

- **Real-world hook**: "Is fluoride in drinking water safe?"
- **Reasoning chain**:
  1. **PRIM-STR005** (structure-to-property): Fluoride ions (F-) interact with the calcium phosphate in tooth enamel. The structural compatibility between F- and the hydroxyapatite crystal lattice means fluoride can substitute into the lattice, forming fluorapatite -- a more acid-resistant mineral.
  2. **PRIM-CHG005** (acid-base reasoning): Tooth decay is caused by acid produced by oral bacteria. Fluorapatite resists acid dissolution better than hydroxyapatite. The fluoride substitution shifts the acid-base equilibrium in favor of enamel preservation.
  3. **DEF-SCL002** (ppm): Fluoride concentration in drinking water is measured in parts per million. The EPA recommends 0.7 ppm for dental protection.
  4. **PRIM-SCL003** (concentration reasoning): At 0.7 ppm, fluoride strengthens enamel without adverse effects. At concentrations above 4 ppm, excess fluoride disrupts enamel formation during tooth development, causing dental fluorosis (mottling, pitting). Same molecule, same chemistry, different outcome -- concentration is the deciding variable.
- **Bridging application**: "Is chlorine in pool water dangerous?" -- Chlorine's structure enables it to act as an oxidizing agent (PRIM-STR005 and PRIM-CHG006): it destroys bacterial cell membranes via redox chemistry. At 1-3 ppm (DEF-SCL002), chlorine kills pathogens without harming swimmers. Above 10 ppm (PRIM-SCL003), the same oxidizing power damages human skin and mucous membranes. Same molecule, same redox mechanism, different dose, different outcome.
- **Tier**: C
- **Significance**: Non-majors are constantly exposed to claims about chemical safety: "chemicals in food," "toxins in water," "safe levels of exposure." This pattern provides the intellectual toolkit to evaluate such claims rationally. Without STR, the student cannot understand *what* the substance does. Without CHG, the student cannot follow the mechanism. Without SCL, every chemical is either "safe" or "dangerous" with no nuance -- and that binary thinking is precisely the scientific illiteracy this course aims to overcome.

---

## CP-006: **Food Chemistry**

- **Domains**: COM x NRG x CHG x SCL
- **Statement**: Given a food preparation or metabolic process, trace the flow of atoms and energy from raw ingredients through chemical transformations to nutritional outcome, using conservation (atoms), energy accounting (bond energy, exo/endo), transformation reasoning (reaction rate), and scale (quantitative energy content).
- **Natural language**: Food is chemistry made personal. Cooking involves providing activation energy (heat) to drive chemical transformations -- proteins denature, starches hydrolyze, sugars caramelize. The atoms in food are conserved through every transformation: what enters as carbohydrate exits as CO2 and H2O. The energy stored in chemical bonds is released during metabolism and measured in Calories. Understanding food chemistry requires tracking atoms (COM), accounting for energy (NRG), describing the transformations (CHG), and quantifying amounts (SCL).
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| COM | PRIM-COM006 (conservation of atoms) |
| NRG | PRIM-NRG002 (bond energy reasoning), PRIM-NRG003 (exo/endothermic classification) |
| CHG | PRIM-CHG004 (rate reasoning) |
| SCL | PRIM-SCL002 (mole concept / amount reasoning) |

- **Real-world hook**: "Why do we cook food?"
- **Reasoning chain**:
  1. **PRIM-CHG004** (rate reasoning): Cooking provides heat, which increases the rate of chemical reactions in food. Raw egg proteins are kinetically stable at room temperature; heating provides the activation energy needed to denature them at a useful rate. Without sufficient temperature, the transformation is too slow to be practical.
  2. **PRIM-NRG002** (bond energy): The chemical bonds in food molecules (proteins, carbohydrates, fats) store energy. During metabolism, these bonds are broken and new, lower-energy bonds form (in CO2 and H2O), releasing the difference as usable energy.
  3. **PRIM-NRG003** (exo/endo): Metabolism is exothermic overall -- the body releases energy as it breaks down food. This released energy powers cellular processes and maintains body temperature.
  4. **PRIM-COM006** (conservation of atoms): Every atom that enters the body as food exits as exhaled CO2, excreted H2O, or waste. Atoms are neither created nor destroyed -- the carbon in a slice of bread becomes the carbon in exhaled CO2.
  5. **PRIM-SCL002** (mole/amount reasoning): A food label listing "200 Calories" quantifies the total energy obtainable from the chemical bonds in that serving. The approximately 2,000 Calories/day recommendation reflects the total bond energy the body needs to extract from food to maintain its functions.
- **Bridging application**: "Why do food labels list Calories?" -- Calories quantify bond energy (PRIM-NRG002) released during the exothermic (PRIM-NRG003) metabolic breakdown of food. The atoms in the food are conserved (PRIM-COM006) -- they are rearranged, not destroyed. The rate of metabolism (PRIM-CHG004) determines how quickly that energy is available. The Calorie count on the label is a macroscopic-scale summary (PRIM-SCL002) of molecular-level energy content.
- **Tier**: C
- **Significance**: This is the most domain-rich composition pattern, requiring all four of COM, NRG, CHG, and SCL. It demonstrates that even the most familiar everyday activity -- eating -- involves sophisticated cross-domain chemistry. For non-majors, food chemistry is the entry point for understanding conservation laws (atoms do not vanish), energy accounting (Calories measure bond energy), reaction kinetics (cooking = increasing rate), and quantitative reasoning (nutritional labels). Removing COM loses atom conservation. Removing NRG loses energy accounting. Removing CHG loses the transformation mechanism. Removing SCL loses the quantitative bridge to nutrition labels.

---

## CP-007: **Biochemistry Connection**

- **Domains**: STR x CHG x SCL
- **Statement**: Given a biological macromolecule (DNA, protein), explain how its large-scale biological function emerges from molecular structure, chemical bonding, and the collective behavior of many subunits.
- **Natural language**: Biological macromolecules like DNA and proteins are polymers -- long chains of repeating monomer units connected by covalent bonds. Their biological function depends critically on their three-dimensional shape, which is determined by specific patterns of intermolecular forces (especially hydrogen bonding) between parts of the molecule. The functional behavior of these molecules (information storage, enzymatic catalysis) is an emergent property that arises only when many structural and chemical features act collectively at macroscopic biological scale.
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| STR | PRIM-STR004 (IMF hierarchy: hydrogen bonding), PRIM-STR005 (structure-to-property inference), DEF-STR007 (carbon backbone reasoning), DEF-STR008 (polymer reasoning) |
| CHG | PRIM-CHG004 (rate reasoning -- enzymatic catalysis context) |
| SCL | PRIM-SCL004 (emergent property reasoning) |

- **Real-world hook**: "Why does DNA have a double helix?"
- **Reasoning chain**:
  1. **DEF-STR008** (polymer reasoning): DNA is a polymer built from nucleotide monomers. Each nucleotide contains a sugar, a phosphate group, and a nitrogenous base, all connected via covalent bonds along a sugar-phosphate backbone.
  2. **DEF-STR007** (carbon backbone): The sugar-phosphate backbone is a carbon-based covalent framework that provides the structural scaffold for the molecule.
  3. **PRIM-STR004** (IMF hierarchy -- hydrogen bonding): Two DNA strands are held together by hydrogen bonds between complementary bases: adenine pairs with thymine via 2 H-bonds; guanine pairs with cytosine via 3 H-bonds. These are intermolecular forces (not covalent bonds), making the double strand separable during replication.
  4. **PRIM-STR005** (structure-to-property): The specific H-bonding pattern determines the double helix shape. The structure directly enables the function: complementary base pairing allows faithful copying of genetic information.
  5. **PRIM-SCL004** (emergence): The information-storage capacity of DNA is an emergent property. A single base pair stores almost no information; 3 billion base pairs encode an entire human genome. The biological function emerges from the collective, ordered arrangement of structural subunits.
- **Bridging application**: "Why do proteins fold into specific shapes?" -- Proteins are polymers of amino acid monomers (DEF-STR008) connected by peptide bonds along a carbon backbone (DEF-STR007). The folded shape is determined by hydrogen bonds, London dispersion forces, and ionic interactions between different parts of the chain (PRIM-STR004). The specific 3D shape determines biological function -- enzyme activity, antibody recognition, structural support (PRIM-STR005). Enzymatic function (catalyzing reactions at biologically useful rates) connects to rate reasoning (PRIM-CHG004). The functional behavior of a folded protein is emergent (PRIM-SCL004): the amino acid sequence alone does not predict function without considering the collective 3D arrangement.
- **Tier**: E
- **Significance**: Biochemistry is the natural capstone application of a non-majors chemistry course. This Enrichment-tier pattern shows students that the same primitives used to explain why ice melts (H-bonding, structure-to-property, emergence) also explain why DNA stores information and why proteins catalyze reactions. It demonstrates the transferability of chemical reasoning from simple systems to the molecular basis of life. The pattern is classified as Enrichment because it requires all prior Core-tier primitives from STR and SCL plus domain knowledge about biological macromolecules, making it suitable for courses with time to extend beyond the Core.

---

## Summary Table

| ID | Name | Domains | Tier | Real-World Hook |
|----|------|---------|------|-----------------|
| CP-001 | Structure-to-Property Prediction | STR x SCL | C | Why does rubbing alcohol evaporate faster than water? |
| CP-002 | Energy-Driven Transformation | NRG x CHG | C | Why does a battery eventually die? |
| CP-003 | Acid-Base in the Body | STR x CHG x SCL | C | Why does aspirin hurt your stomach but an antacid helps? |
| CP-004 | Greenhouse Effect | STR x NRG x SCL | C | Why is CO2 a greenhouse gas but N2 is not? |
| CP-005 | Dose Makes the Poison | STR x CHG x SCL | C | Is fluoride in drinking water safe? |
| CP-006 | Food Chemistry | COM x NRG x CHG x SCL | C | Why do we cook food? |
| CP-007 | Biochemistry Connection | STR x CHG x SCL | E | Why does DNA have a double helix? |

### Domain Coverage Matrix

Every domain appears in at least two composition patterns, confirming that no domain is isolated from cross-domain reasoning:

| Domain | Patterns |
|--------|----------|
| COM | CP-006 |
| STR | CP-001, CP-003, CP-004, CP-005, CP-007 |
| NRG | CP-002, CP-004, CP-006 |
| CHG | CP-002, CP-003, CP-005, CP-006, CP-007 |
| SCL | CP-001, CP-003, CP-004, CP-005, CP-006, CP-007 |

### Irreducibility Check

Each pattern has been verified to be irreducibly cross-domain. For each pattern, removing any participating domain breaks the reasoning chain:

- **CP-001**: Without STR, no molecular explanation for property differences. Without SCL, no bridge to bulk observation.
- **CP-002**: Without NRG, no thermodynamic driving force. Without CHG, no reaction mechanism or equilibrium.
- **CP-003**: Without STR, no explanation for acid/base identity. Without CHG, no proton-transfer mechanism. Without SCL, no dose-response reasoning.
- **CP-004**: Without STR, no explanation for IR absorption selectivity. Without NRG, no absorption mechanism. Without SCL, no planetary-scale consequence.
- **CP-005**: Without STR, no explanation for molecular activity. Without CHG, no reaction mechanism. Without SCL, no dose distinction.
- **CP-006**: Without COM, no atom conservation. Without NRG, no energy accounting. Without CHG, no transformation mechanism. Without SCL, no quantitative nutritional reasoning.
- **CP-007**: Without STR, no structural explanation. Without CHG, no connection to catalytic function. Without SCL, no emergence of biological function.
