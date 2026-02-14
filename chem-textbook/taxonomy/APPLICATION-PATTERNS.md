# APPLICATION DEPLOYMENT PATTERNS v0.1

Worked application deployment patterns for the chemistry taxonomy. Each pattern deploys one of the seven composition patterns (CP-001 through CP-007) from COMPOSITION-PATTERNS.md using the four-step pedagogical sequence: name the primitives, present the hook, walk through the composition, bridge to a second application.

**Total**: 7 patterns (ADP-001 through ADP-007)

**Governing principle**: Applications are deployment exercises for named primitives, not the organizational backbone (ASM-GLB004). The two-application structure per pattern solves the situatedness paradox (SRC-GLB006): students see the same reasoning tools transfer across contexts, proving the primitives are general-purpose.

---

## ADP-001: Structure Predicts Behavior (deploys CP-001)

### Step 1 -- Name the Primitives
- **PRIM-STR004** (intermolecular force hierarchy): Given two substances, classify the dominant intermolecular forces in each to determine which has stronger molecular attractions.
- **PRIM-STR005** (structure-to-property inference): Given a molecular structure and its IMF profile, infer the resulting physical property (boiling point, evaporation rate, solubility).
- **PRIM-SCL001** (macro-to-submicro translation): Given a macroscopic observation, translate it to a molecular-level explanation, or vice versa.
- **PRIM-SCL004** (emergent property reasoning): Given a molecular-level behavior, recognize that the bulk property emerges from the collective action of billions of molecules.

### Step 2 -- The Hook
Why does rubbing alcohol evaporate faster than water? You spill both on your hand -- the alcohol vanishes in seconds, but the water lingers. They are both clear liquids at room temperature. What is different about them at the molecular level?

### Step 3 -- Composition Walkthrough
Using **intermolecular force hierarchy** (PRIM-STR004), we classify the attractions in each liquid: water molecules form extensive hydrogen bonds with each other (strong IMFs), while isopropanol molecules have fewer hydrogen bonds and rely more on weaker London dispersion forces. Applying **structure-to-property inference** (PRIM-STR005), we reason that weaker IMFs mean molecules need less energy to escape from the liquid surface, so isopropanol molecules escape more readily. We then perform a **macro-to-submicro translation** (PRIM-SCL001): the molecular-level conclusion (easier escape per molecule) maps onto the macroscopic observation (faster evaporation on your skin). Finally, **emergent property reasoning** (PRIM-SCL004) reminds us that the evaporation rate we observe is not the behavior of one molecule but the collective result of billions of molecules, each governed by the same IMF balance.

### Step 4 -- The Bridge
Why don't oil and water mix? Using **intermolecular force hierarchy** (PRIM-STR004), we identify that water has strong hydrogen bonding while oil (nonpolar hydrocarbons) has only weak London dispersion forces. **Structure-to-property inference** (PRIM-STR005) tells us that mixing would require breaking water's hydrogen-bond network without comparable replacement attractions -- an energetically unfavorable trade. The **macro-to-submicro translation** (PRIM-SCL001) connects the molecular incompatibility to the visible phase separation in a salad dressing bottle, and **emergent property reasoning** (PRIM-SCL004) confirms this is a collective phenomenon: every water molecule preferentially interacts with other water molecules, producing the macroscopic oil-on-top layer.

### Why This Bridge Works
Both applications require the same four-primitive reasoning chain -- classify IMFs, infer the property consequence, translate between scales, and recognize emergence -- despite one involving evaporation rate and the other involving solubility.

---

## ADP-002: Energy Drives Change (deploys CP-002)

### Step 1 -- Name the Primitives
- **PRIM-NRG005** (spontaneity reasoning): Given a process, determine whether it is thermodynamically favorable by considering enthalpy and entropy together.
- **PRIM-NRG003** (exo/endothermic classification): Given a process, classify whether energy is released to or absorbed from the surroundings.
- **PRIM-CHG003** (equilibrium reasoning): Given a reversible process, determine where the system ends up by reasoning about the balance between forward and reverse directions.
- **PRIM-CHG006** (oxidation-reduction reasoning): Given a chemical system, identify what is being oxidized and what is being reduced to trace the electron flow.

### Step 2 -- The Hook
Why does a battery eventually die? You charge your phone, use it all day, and the battery drains to zero. What is happening inside that battery at the chemical level, and why does it eventually stop producing electricity?

### Step 3 -- Composition Walkthrough
Using **oxidation-reduction reasoning** (PRIM-CHG006), we identify the battery as a system running a spontaneous redox reaction: one electrode material loses electrons (is oxidized) while another gains them (is reduced), and the electron flow through the external circuit is the electricity that powers your phone. **Spontaneity reasoning** (PRIM-NRG005) explains why this happens at all: the reaction is thermodynamically favorable, meaning the products are at lower free energy than the reactants, so the system naturally moves in the forward direction. **Exo/endothermic classification** (PRIM-NRG003) tells us the process is exothermic overall -- stored chemical energy is converted to electrical energy and some heat. Then **equilibrium reasoning** (PRIM-CHG003) explains the death of the battery: as reactants are consumed and products accumulate, the driving force diminishes until the system reaches equilibrium, where no net reaction occurs and no current flows.

### Step 4 -- The Bridge
Why does ice melt at room temperature? **Spontaneity reasoning** (PRIM-NRG005) reveals that above 0 degrees C, the entropy gain from disordering the rigid ice lattice outweighs the enthalpy cost of breaking hydrogen bonds, making melting thermodynamically favorable. **Exo/endothermic classification** (PRIM-NRG003) tells us the process is endothermic -- the ice absorbs heat from the warmer surroundings, which is why a glass of ice water feels cold. **Equilibrium reasoning** (PRIM-CHG003) shows that at room temperature, the equilibrium overwhelmingly favors liquid water, so the process goes essentially to completion.

### Why This Bridge Works
Both a dying battery and melting ice are spontaneous processes driven to completion (or equilibrium) by the same energy-and-transformation logic, despite one being a redox reaction producing electricity and the other being a physical phase change absorbing heat.

---

## ADP-003: Acids, Bases, and Your Body (deploys CP-003)

### Step 1 -- Name the Primitives
- **PRIM-STR002** (bond polarity reasoning): Given a molecular structure, identify polar bonds to determine which atoms can donate or accept protons.
- **PRIM-STR005** (structure-to-property inference): Given a structural feature, infer the chemical behavior it enables (acid donation, base acceptance).
- **PRIM-CHG005** (acid-base reasoning): Given an acid-base system, trace the proton transfer to determine which species donates H+ and which accepts it.
- **DEF-CHG002** (pH scale): The logarithmic scale that quantifies acidity; lower pH means more acidic, higher pH means more basic.
- **PRIM-SCL003** (concentration reasoning): Given a substance and its amount, determine how concentration affects the severity of the chemical outcome.

### Step 2 -- The Hook
Why does aspirin hurt your stomach but an antacid helps? Both are pills you swallow, both dissolve in the same stomach fluid, yet one causes pain and the other relieves it. What makes them chemical opposites?

### Step 3 -- Composition Walkthrough
Using **bond polarity reasoning** (PRIM-STR002) and **structure-to-property inference** (PRIM-STR005), we identify that aspirin contains a carboxylic acid group (-COOH) with a polar O-H bond capable of releasing H+ ions; this structural feature makes aspirin an acid. **Acid-base reasoning** (PRIM-CHG005) traces the proton transfer: in the stomach, aspirin donates H+ ions, increasing the local acidity beyond what the stomach lining can comfortably handle. The **pH scale** (DEF-CHG002) quantifies the damage -- aspirin pushes the local pH lower, meaning more acidic. **Concentration reasoning** (PRIM-SCL003) explains dose-dependence: one tablet causes mild irritation, but taking several on an empty stomach can overwhelm the stomach's buffering capacity. An antacid like Mg(OH)2 deploys the same acid-base reasoning in reverse (PRIM-CHG005): it accepts H+ ions, neutralizing the excess acid and raising pH back toward normal.

### Step 4 -- The Bridge
Why does lemon juice taste sour but soap feels slippery? Lemon juice contains citric acid, whose structure features three carboxylic acid groups (PRIM-STR002, PRIM-STR005) that donate H+ ions in solution (PRIM-CHG005), producing a low pH (DEF-CHG002) that taste receptors detect as sour. Soap retains traces of sodium hydroxide from its manufacturing, which accepts H+ and produces a high pH -- the slippery feel is your skin's oils being saponified by the base. The intensity of sourness or slipperiness scales directly with concentration (PRIM-SCL003): concentrated lemon juice is more sour, and industrial-strength soap solution is dangerously slippery.

### Why This Bridge Works
Aspirin-vs-antacid and lemon-vs-soap are both acid-base pairs whose behavior is explained by the identical five-step chain: structure determines acid/base identity, proton transfer determines the reaction, pH quantifies the result, and concentration determines the intensity.

---

## ADP-004: Why Some Gases Warm the Planet (deploys CP-004)

### Step 1 -- Name the Primitives
- **PRIM-STR003** (molecular shape reasoning): Given a molecular formula, determine the 3D arrangement of atoms to identify possible vibrational modes.
- **PRIM-STR002** (bond polarity reasoning): Given a bond between two atoms, determine whether the bond is polar (unequal electron sharing) or nonpolar.
- **PRIM-NRG002** (bond energy reasoning): Given a molecule exposed to infrared radiation, determine whether its bond vibrations can absorb the photon's energy.
- **PRIM-SCL004** (emergent property reasoning): Given a molecular-level behavior and an atmospheric concentration, determine the collective macroscopic consequence.

### Step 2 -- The Hook
Why is CO2 a greenhouse gas but N2 is not? Both are invisible gases in the air you breathe. Nitrogen makes up 78% of the atmosphere, while CO2 is only 0.04%. Yet CO2 drives global warming and N2 does not. What molecular difference explains this?

### Step 3 -- Composition Walkthrough
Using **bond polarity reasoning** (PRIM-STR002), we identify that CO2 has polar C=O bonds (oxygen pulls electrons more strongly than carbon), while N2 has a completely nonpolar N-N bond (identical atoms share electrons equally). **Molecular shape reasoning** (PRIM-STR003) reveals a critical subtlety: CO2 is linear and symmetric overall, but when it vibrates asymmetrically (one C=O stretching while the other compresses), a temporary change in dipole moment occurs; N2, with no bond polarity at all, cannot produce a dipole change no matter how it vibrates. **Bond energy reasoning** (PRIM-NRG002) explains the mechanism: when infrared radiation from Earth's surface hits a CO2 molecule and matches its vibrational frequency, the molecule absorbs the photon's energy; N2 is transparent to infrared because it has no dipole-active vibrations. Finally, **emergent property reasoning** (PRIM-SCL004) bridges from one molecule to a planet: a single CO2 absorption event is negligible, but 420+ ppm of CO2 means trillions upon trillions of molecules collectively trapping and re-emitting thermal radiation, producing measurable atmospheric warming.

### Step 4 -- The Bridge
Why is methane worse than CO2 for climate? Methane (CH4) has four polar C-H bonds (PRIM-STR002) arranged in a tetrahedral shape (PRIM-STR003), giving it multiple IR-active vibrational modes that absorb across a wider range of infrared wavelengths (PRIM-NRG002). Per molecule, methane is roughly 80 times more potent as a greenhouse gas over 20 years. Even at concentrations far lower than CO2, methane's superior per-molecule absorption makes its collective atmospheric impact (PRIM-SCL004) disproportionately large.

### Why This Bridge Works
Both applications ask "why does this gas trap heat?" and both are answered by the identical chain: bond polarity determines whether dipole changes are possible, molecular shape determines which vibrations are IR-active, energy reasoning explains the absorption mechanism, and emergence scales the molecular event to a planetary consequence.

---

## ADP-005: The Dose Makes the Poison (deploys CP-005)

### Step 1 -- Name the Primitives
- **PRIM-STR005** (structure-to-property inference): Given a molecular structure, infer what chemical interactions it can participate in within a biological system.
- **PRIM-CHG005** (acid-base reasoning): Given an acid-base system, trace the proton transfer and its biological consequence. (Or PRIM-CHG006, oxidation-reduction reasoning, depending on the application.)
- **PRIM-SCL003** (concentration reasoning): Given a substance at a specific dose, determine whether the concentration falls in the beneficial, neutral, or harmful range.
- **DEF-SCL002** (parts per million/billion): The unit system for expressing trace concentrations relevant to safety and toxicology.

### Step 2 -- The Hook
Is fluoride in drinking water safe? Some communities add fluoride; others ban it. News headlines call it both "essential for dental health" and "a toxic chemical." How can the same substance be both? The answer is not politics -- it is chemistry.

### Step 3 -- Composition Walkthrough
Using **structure-to-property inference** (PRIM-STR005), we identify that fluoride ions (F-) are structurally compatible with hydroxyapatite, the calcium phosphate mineral in tooth enamel; fluoride can substitute into the crystal lattice, forming fluorapatite, a harder, more acid-resistant mineral. **Acid-base reasoning** (PRIM-CHG005) reveals why this matters: tooth decay is caused by acids produced by oral bacteria, and fluorapatite resists acid dissolution better than the original hydroxyapatite, shifting the acid-base equilibrium in favor of enamel preservation. **Parts per million** (DEF-SCL002) gives us the measurement framework: municipal water fluoridation operates at about 0.7 ppm. **Concentration reasoning** (PRIM-SCL003) delivers the verdict: at 0.7 ppm, fluoride strengthens enamel with no adverse effects; above 4 ppm, the same ion disrupts enamel formation during childhood tooth development, causing fluorosis. Same molecule, same chemistry, opposite outcomes -- concentration is the only variable that changed.

### Step 4 -- The Bridge
Is chlorine in pool water dangerous? **Structure-to-property inference** (PRIM-STR005) tells us that chlorine-based compounds (like hypochlorous acid) are strong oxidizing agents capable of disrupting bacterial cell membranes. **Oxidation-reduction reasoning** (PRIM-CHG006) traces the mechanism: chlorine strips electrons from organic molecules in pathogens, destroying them. At 1-3 ppm (DEF-SCL002), this oxidizing power selectively kills bacteria without harming swimmers. Above 10 ppm (PRIM-SCL003), the same oxidizing chemistry attacks human skin and mucous membranes. Same molecule, same mechanism, different dose, different outcome.

### Why This Bridge Works
Both fluoride and chlorine are chemicals whose safety depends entirely on concentration, and both require the identical reasoning chain -- structure determines what the molecule can do, change reasoning explains how it acts, and scale determines whether the outcome is beneficial or harmful.

---

## ADP-006: The Chemistry of Your Kitchen (deploys CP-006)

### Step 1 -- Name the Primitives
- **PRIM-COM006** (conservation of atoms): Given a chemical transformation, track every atom from reactants to products; atoms are rearranged, never created or destroyed.
- **PRIM-NRG002** (bond energy reasoning): Given a set of chemical bonds, determine the energy stored in them and released when they break and reform.
- **PRIM-NRG003** (exo/endothermic classification): Given a process, classify whether energy flows out to (exothermic) or in from (endothermic) the surroundings.
- **PRIM-CHG004** (rate reasoning): Given a reaction and a temperature, determine how temperature affects the speed of the chemical transformation.
- **PRIM-SCL002** (mole concept / amount reasoning): Given a quantity of substance, relate the molecular-level energy content to the macroscopic measurement on a food label.

### Step 2 -- The Hook
Why do we cook food? Humans are the only species that routinely transforms food with heat before eating it. Raw chicken is dangerous, but cooked chicken is safe. Raw egg is gooey, but a fried egg is solid. What is heat actually doing to the molecules in your food?

### Step 3 -- Composition Walkthrough
Using **rate reasoning** (PRIM-CHG004), we recognize that cooking provides heat energy, which dramatically increases the speed of chemical reactions in food -- proteins unfold (denature), starches break down (hydrolyze), and sugars undergo browning (Maillard reactions) -- all of which are too slow at room temperature to occur on a useful timescale. **Bond energy reasoning** (PRIM-NRG002) explains what happens during metabolism: the chemical bonds in carbohydrates, fats, and proteins store energy; when your body breaks these bonds and forms new, lower-energy bonds in CO2 and H2O, the energy difference is released for your cells to use. **Exo/endothermic classification** (PRIM-NRG003) confirms that metabolism is exothermic overall -- the body releases energy, which is why you are warm. **Conservation of atoms** (PRIM-COM006) ensures nothing vanishes: every carbon atom in that slice of bread eventually leaves your body as CO2 in exhaled breath, and every hydrogen atom leaves as H2O. Finally, **amount reasoning** (PRIM-SCL002) connects the molecular story to the number on the package: a food label listing "200 Calories" quantifies the total bond energy available in that serving, and the 2,000 Calorie/day guideline reflects the total energy your body needs to extract from food daily.

### Step 4 -- The Bridge
Why do food labels list Calories? A Calorie count is a macroscopic summary (PRIM-SCL002) of molecular-level **bond energy** (PRIM-NRG002): it measures the total energy your body can release by metabolizing that food in an **exothermic** (PRIM-NRG003) series of reactions. The **rate** (PRIM-CHG004) of those metabolic reactions determines how quickly the energy becomes available -- simple sugars metabolize fast (quick energy spike), while complex carbohydrates metabolize slowly (sustained energy). Through it all, **conservation of atoms** (PRIM-COM006) holds: every atom in the food is accounted for in the metabolic products.

### Why This Bridge Works
Cooking and Calorie counting are two faces of the same five-primitive reasoning chain: both require tracking atoms through transformations, accounting for energy in bonds, classifying energy flow direction, understanding reaction rates, and bridging from molecules to macroscopic quantities.

---

## ADP-007: Chemistry Meets Biology (deploys CP-007)

### Step 1 -- Name the Primitives
- **PRIM-STR004** (intermolecular force hierarchy): Given a macromolecule, identify which intermolecular forces (especially hydrogen bonding) hold its 3D structure together.
- **PRIM-STR005** (structure-to-property inference): Given a 3D molecular structure, infer the biological function it enables.
- **DEF-STR007** (carbon backbone reasoning): Recognize that biological macromolecules are built on carbon-based covalent frameworks.
- **DEF-STR008** (polymer reasoning): Recognize that large biological molecules are polymers -- long chains of repeating monomer subunits.
- **PRIM-CHG004** (rate reasoning): Given a biological catalyst (enzyme), reason about how it accelerates reaction rates.
- **PRIM-SCL004** (emergent property reasoning): Given many molecular subunits acting collectively, recognize that biological function emerges from their ordered arrangement.

### Step 2 -- The Hook
Why does DNA have a double helix? You have seen the iconic twisted-ladder image, but why that particular shape? It is not decorative -- the shape is a direct consequence of chemistry, and the shape is what makes genetic information storage possible.

### Step 3 -- Composition Walkthrough
Using **polymer reasoning** (DEF-STR008), we recognize DNA as a polymer: a long chain of nucleotide monomers, each containing a sugar, a phosphate group, and a nitrogenous base, linked by covalent bonds. **Carbon backbone reasoning** (DEF-STR007) identifies the sugar-phosphate backbone as the structural scaffold -- a carbon-based covalent framework that gives the molecule its spine. The **intermolecular force hierarchy** (PRIM-STR004) explains the double helix: two DNA strands are held together by hydrogen bonds between complementary bases (adenine with thymine via 2 H-bonds, guanine with cytosine via 3 H-bonds). These are intermolecular forces, not covalent bonds, which is why the two strands can separate during replication without breaking the backbone. **Structure-to-property inference** (PRIM-STR005) delivers the payoff: the specific base-pairing pattern is not arbitrary -- it enables faithful copying of genetic information, because each strand serves as a template for the other. Finally, **emergent property reasoning** (PRIM-SCL004) explains why this matters at the biological scale: a single base pair stores almost no information, but 3 billion base pairs in ordered sequence encode the entire human genome. The information-storage function emerges only from the collective, ordered arrangement.

### Step 4 -- The Bridge
Why do proteins fold into specific shapes? Proteins are **polymers** (DEF-STR008) of amino acid monomers connected by peptide bonds along a **carbon backbone** (DEF-STR007). The folded 3D shape is determined by hydrogen bonds, London dispersion forces, and ionic interactions between different parts of the amino acid chain (**intermolecular force hierarchy**, PRIM-STR004). The specific shape directly determines function: an enzyme's active site must have exactly the right geometry to catalyze its target reaction, which connects to **rate reasoning** (PRIM-CHG004) -- enzymes accelerate biological reactions by factors of millions. The biological function of a folded protein is **emergent** (PRIM-SCL004): the amino acid sequence alone does not reveal function without the collective 3D arrangement.

### Why This Bridge Works
DNA's double helix and protein folding are both explained by the same reasoning chain: polymer structure provides the backbone, intermolecular forces determine the 3D shape, structure dictates function, and biological capability emerges from the collective arrangement of molecular subunits.

---

## Summary Table

| ID | Title | Deploys | Hook | Bridge |
|----|-------|---------|------|--------|
| ADP-001 | Structure Predicts Behavior | CP-001 (STR x SCL) | Why does rubbing alcohol evaporate faster than water? | Why don't oil and water mix? |
| ADP-002 | Energy Drives Change | CP-002 (NRG x CHG) | Why does a battery eventually die? | Why does ice melt at room temperature? |
| ADP-003 | Acids, Bases, and Your Body | CP-003 (STR x CHG x SCL) | Why does aspirin hurt your stomach but an antacid helps? | Why does lemon juice taste sour but soap feels slippery? |
| ADP-004 | Why Some Gases Warm the Planet | CP-004 (STR x NRG x SCL) | Why is CO2 a greenhouse gas but N2 is not? | Why is methane worse than CO2 for climate? |
| ADP-005 | The Dose Makes the Poison | CP-005 (STR x CHG x SCL) | Is fluoride in drinking water safe? | Is chlorine in pool water dangerous? |
| ADP-006 | The Chemistry of Your Kitchen | CP-006 (COM x NRG x CHG x SCL) | Why do we cook food? | Why do food labels list Calories? |
| ADP-007 | Chemistry Meets Biology | CP-007 (STR x CHG x SCL) | Why does DNA have a double helix? | Why do proteins fold into specific shapes? |

### Pedagogical Design Notes

1. **Every ADP uses the same four-step sequence.** This consistency is intentional: students internalize the meta-pattern (name tools, apply them, see them transfer) alongside the chemistry content.

2. **Primitives are bolded and named in-line.** Students encounter the primitive as a labeled reasoning tool at the moment they use it. This solves the visibility problem: the conceptual machinery is not hidden behind jargon but displayed as explicit, reusable moves.

3. **The bridge is the key pedagogical move.** A single application can be dismissed as "just memorize the answer." Two applications using the same primitives prove the reasoning is general. This is the mechanism by which the taxonomy solves the situatedness paradox (SRC-GLB006, SRC-GLB007).

4. **Non-majors calibration is maintained throughout.** No walkthrough requires calculus. All reasoning is qualitative or proportional. Jargon is introduced only when accompanied by a plain-language explanation.
