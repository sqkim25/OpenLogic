# DOMAIN-SCL v0.1

## 0. Sources & Assumptions

- SRC-SCL001: Arons, *Teaching Introductory Physics*, 1997, Ch. 1--3 (proportional reasoning, unit analysis, scaling arguments -- physics text but the reasoning pedagogy transfers directly to chemistry)
- SRC-SCL002: Laugier & Dumon, "The equation of reaction: A cluster of obstacles," *Chemistry Education Research and Practice*, 2004 (mole concept misconceptions and proportional reasoning failures)
- SRC-GLB003: Johnstone, "Why is science difficult to learn?", *J. Computer Assisted Learning*, 1991
- SRC-GLB008: OpenStax, *Chemistry 2e*, 2019, Ch. 3 (moles, molar mass), Ch. 4 (solutions, concentration), Ch. 9 (ideal gas)
- SRC-GLB009: Zumdahl & Zumdahl, *Chemistry*, 10th ed., 2017, Ch. 3 (stoichiometry), Ch. 4 (solutions), Ch. 5 (gases)
- ASM-SCL001: Students possess basic proportional reasoning ability (the capacity to set up and solve ratios like a/b = c/d) but may not spontaneously apply it to chemical contexts. Justification: proportional reasoning is a prerequisite for algebra (ASM-GLB002), so it is within the assumed math ceiling, but its deployment in chemistry-specific contexts (moles, dilution, stoichiometry) must be explicitly taught (SRC-SCL002).
- ASM-SCL002: Students can read a graduated cylinder, a balance, and a thermometer, but we do not assume familiarity with any chemistry-specific measurement technique (titration, spectrophotometry, gas collection). Justification: non-majors labs vary widely in equipment; the taxonomy builds from general measurement literacy upward.

## 1. Domain Intent

- **Governing question**: How do molecular-level events produce the macroscopic phenomena we observe and measure?
- **Scope**: Translating between the submicroscopic world (atoms, molecules, formula units) and the macroscopic world (grams, liters, observable properties). SCL provides the quantitative bridge: the mole concept, concentration reasoning, proportional reasoning, unit analysis, and emergent property reasoning. SCL also owns safety and risk reasoning, which depends on concentration and exposure -- inherently scale-dependent concepts.
- **Non-goals**: What atoms are present or what type of substance it is (COM). How atoms are arranged in three dimensions (STR). Why processes are energetically favorable (NRG). What reacts with what and how fast (CHG).
- **Dissolution argument**: Scale reasoning is about TRANSLATION between molecular and macroscopic descriptions. You can know everything about the hydrogen bonds in water (STR) without understanding why ice floats -- that requires reasoning about how molecular-level arrangement scales to bulk density, a bridging operation that is not derivable from any single molecular-level domain. The mole concept, concentration reasoning, proportional reasoning, and unit analysis are general quantitative tools for converting between "number of particles" and "weighable, measurable amounts." These tools do not require molecular geometry (STR), energy concepts (NRG), or transformation mechanics (CHG) to define. They require only the identity of what is being counted (COM). Merging SCL into COM would conflate "what is it?" with "how much of it, and what does that amount produce at bulk?" -- two distinct cognitive operations that Johnstone's triplet model (SRC-GLB003) identifies as the macro/submicro translation, the single most difficult reasoning move in chemistry.
- **Threshold schema mapping**: Centralized --> Decentralized. The foundational conceptual shift in SCL is recognizing that no single molecule controls bulk behavior -- macroscopic properties emerge from the collective, statistical behavior of enormous numbers of molecules. A single water molecule has no boiling point; boiling point is a property of 10^23 molecules interacting simultaneously. Students who fail to cross this threshold expect every macroscopic property to be traceable to a single molecule's feature, missing the essential role of scale and aggregation.

## 2. Prerequisites

- **DEP-SCL001**: COM -- SCL imports PRIM-COM001 (atomic composition analysis) and PRIM-COM005 (chemical formula reading). These are the identity and counting tools that SCL bridges to macroscopic quantities. SCL also imports PRIM-COM008 (causal chain reasoning) as the meta-reasoning skill for connecting molecular events to macroscopic observations.

SCL does NOT depend on STR, NRG, or CHG. The mole concept, concentration reasoning, proportional reasoning, and unit analysis are general bridging tools between submicroscopic and macroscopic descriptions. They require knowing WHAT is being counted (COM), but not HOW it is arranged (STR), what ENERGY is involved (NRG), or what TRANSFORMATION occurs (CHG).

## 3. Primitives

- PRIM-SCL001: **Macro-to-submicro translation**
  - Reasoning move: Given an observable macroscopic property (color, boiling point, solubility, density) or a molecular-level behavior (bond rotation, intermolecular attraction, electron transfer), translate between the two levels -- explaining the macroscopic in terms of the molecular, or predicting the macroscopic from the molecular.
  - Description: The cognitive operation of bridging Johnstone's two levels. This is the single most important -- and most difficult -- reasoning move in introductory chemistry. Every time a student answers "why does X happen?" in chemistry, they must connect a submicroscopic event (molecular-level) to a macroscopic observation (lab-bench-level). The translation goes both directions: top-down (why does ice float? Because the molecular arrangement of solid water creates open hexagonal channels that lower density) and bottom-up (water molecules form hydrogen bonds; predict: water should have an unusually high boiling point for its molecular weight). This primitive does not require knowing the specific molecular-level details (those come from COM, STR, NRG, or CHG) -- it is the bridging operation itself: the cognitive move of connecting levels.
  - Semi-formal: Given an observation O at the macroscopic level, identify the molecular-level feature M that explains O: O = MacroManifestation(M). Conversely, given a molecular-level feature M, predict the macroscopic consequence: O = MacroManifestation(M). The translation function MacroManifestation maps individual-molecule behaviors to bulk, statistical outcomes.
  - Depends: PRIM-COM001 (imported -- must know what atoms/molecules are present before translating between levels)
  - Ownership: SCL
  - Source: SRC-GLB003 (Johnstone 1991, macro/submicro distinction), SRC-GLB008 (OpenStax Ch. 1)
  - Referenced by: --
  - Tier: C
  - Real-world hook: A pot of water boils at 100 degrees C. Macro-to-submicro translation asks: what are the water molecules doing at the molecular level? They are gaining enough kinetic energy to overcome hydrogen bonds and escape into the gas phase. Without this translation, "boiling" is just a thing that happens; with it, you can predict that dissolving salt will raise the boiling point (because dissolved particles interfere with surface escape).

- PRIM-SCL002: **Mole concept**
  - Reasoning move: Given a number of atoms, molecules, or formula units, convert to moles (divide by 6.02 x 10^23); given moles, convert to mass using molar mass -- thereby bridging the uncountable particle world to the weighable lab world.
  - Description: The mole is chemistry's counting unit, defined as exactly 6.02214076 x 10^23 entities (Avogadro's number, N_A). Just as a "dozen" converts between individual eggs and cartons, a "mole" converts between individual molecules and grams. The mole concept is the essential quantitative bridge in chemistry: without it, there is no way to connect a balanced equation (which talks about molecules) to a laboratory measurement (which talks about grams). The mole concept depends on knowing what formula you are counting (PRIM-COM005, imported) and on the general principle that molecular-level counts must be translated to macroscopic quantities (PRIM-SCL001).
  - Semi-formal: For a substance with formula F and molar mass M_F (grams per mole): n = N / N_A (moles from particle count) and mass = n x M_F (grams from moles). Conversely, n = mass / M_F and N = n x N_A. N_A = 6.02214076 x 10^23 mol^(-1).
  - Depends: PRIM-COM005 (imported -- must read the formula to determine molar mass), PRIM-SCL001 (macro-to-submicro translation -- the mole is the quantitative implementation of that bridge)
  - Ownership: SCL
  - Source: SRC-GLB008 (OpenStax Ch. 3), SRC-GLB009 (Zumdahl Ch. 3), SRC-SCL002 (Laugier & Dumon 2004, mole misconceptions)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: A recipe calls for "1 cup of sugar." A chemist's recipe (a balanced equation) calls for "1 mole of glucose." Both are counting instructions: 1 cup is approximately 200 g of sugar, and 1 mole of glucose (C6H12O6) is 180 g. The mole lets you "measure out" the right number of molecules using a balance instead of counting 6 x 10^23 particles one by one.

- PRIM-SCL003: **Concentration reasoning**
  - Reasoning move: Given a solution, determine the amount of solute per volume of solution (concentration); predict how changing concentration affects rate, biological activity, toxicity, or any concentration-dependent property.
  - Description: The cognitive operation of reasoning about how much of a substance is dissolved in how much solvent, and why this ratio -- not just the identity or the total amount -- determines the effect. A drop of bleach in a swimming pool is harmless; the same bleach undiluted burns skin. The substance is the same; the concentration is different. This primitive captures the reasoning that "the dose makes the poison" (Paracelsus): biological and chemical effects depend on amount per volume, not just amount. Concentration reasoning is essential for interpreting medication dosages, pollution levels, and any claim about chemical exposure.
  - Semi-formal: Concentration c of solute X in solution S: c = amount(X) / volume(S). Common units: mol/L (molarity, M), g/L, mg/L, ppm, ppb. For a concentration-dependent property P: P = f(c), where f is typically monotonic (more concentrated = stronger effect) but may saturate or exhibit threshold behavior. Dilution: c_1 V_1 = c_2 V_2 (amount of solute is conserved).
  - Depends: PRIM-SCL002 (mole concept -- concentration is typically expressed in moles per liter)
  - Ownership: SCL
  - Source: SRC-GLB008 (OpenStax Ch. 4), SRC-GLB009 (Zumdahl Ch. 4)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: A city's water report says "lead: 12 ppb." Is that dangerous? The EPA action level is 15 ppb. Concentration reasoning tells you: 12 ppb is below the threshold, but close. If you run the tap for 30 seconds first (flushing stagnant water), the concentration drops. Without concentration reasoning, "lead in the water" sounds equally terrifying whether it is 1 ppb or 1000 ppb.

- PRIM-SCL004: **Emergent property reasoning**
  - Reasoning move: Given molecular-level features, explain why the bulk (macroscopic) property is NOT a simple sum or average of individual-molecule properties -- the whole behaves differently from any single part.
  - Description: The cognitive operation of recognizing emergence: a property that exists only at the collective level and cannot be attributed to any single molecule. One water molecule does not have a melting point, surface tension, or viscosity. These properties arise only when enormous numbers of molecules interact simultaneously, and the bulk behavior is qualitatively different from the behavior of any individual molecule. Emergent property reasoning is the conceptual companion to PRIM-SCL001 (macro-to-submicro translation): while PRIM-SCL001 provides the general translation operation, PRIM-SCL004 captures the specific insight that some properties ONLY exist at the macro level and require collective behavior to explain. This is what makes the "centralized --> decentralized" threshold schema concrete.
  - Semi-formal: A property P is emergent if: (1) P is not definable for a single molecule m in isolation, and (2) P arises from the collective statistical behavior of N molecules where N >> 1. Examples: boiling point, viscosity, color of a metal, electrical conductivity, surface tension. Non-examples: molecular mass (definable for one molecule), bond angle (definable for one molecule).
  - Depends: PRIM-SCL001 (macro-to-submicro translation -- must have the general bridging operation before identifying which properties require collective behavior)
  - Ownership: SCL
  - Source: SRC-GLB003 (Johnstone 1991), SRC-GLB005 (Talanquer 2015, threshold schema: emergent properties)
  - Referenced by: --
  - Tier: C
  - Real-world hook: A single gold atom is not shiny and is not yellow. Gold's characteristic color and luster emerge from the collective behavior of trillions of atoms interacting with light through their delocalized electrons. Similarly, a single water molecule is not wet. "Wetness" is an emergent property of vast numbers of water molecules interacting with a surface via cohesive and adhesive forces.

- PRIM-SCL005: **Proportional reasoning**
  - Reasoning move: Given a ratio or proportion relating two quantities (molecular ratio from a balanced equation, dilution factor, unit conversion factor), scale it up or down to connect molecular-level ratios to lab-scale quantities.
  - Description: The cognitive operation of using ratios to move between scales. In chemistry, proportional reasoning shows up everywhere: stoichiometric ratios (2 mol H2 per 1 mol O2), dilution calculations (c1V1 = c2V2), unit conversions (1 kg = 1000 g), and scaling recipes up or down. This primitive is the quantitative workhorse of SCL: once you have the mole concept (PRIM-SCL002), proportional reasoning is how you actually USE it to calculate how much reagent you need, how much product you will get, or how to prepare a solution of desired concentration. The reasoning move itself is domain-general (it is the same cognitive operation in cooking, pharmacy, and engineering), but its deployment in chemistry is distinctive because the ratios come from balanced equations and molar masses.
  - Semi-formal: Given a proportion a/b = c/d where three of the four values are known, solve for the fourth. In stoichiometry: mol(A)/coeff(A) = mol(B)/coeff(B), where coeff values come from the balanced equation. In dilution: c_1 V_1 = c_2 V_2. In unit conversion: quantity_new = quantity_old x (conversion factor).
  - Depends: PRIM-SCL002 (mole concept -- proportional reasoning in chemistry uses mole ratios as the primary proportion)
  - Ownership: SCL
  - Source: SRC-SCL001 (Arons 1997, proportional reasoning pedagogy), SRC-GLB008 (OpenStax Ch. 3), SRC-SCL002 (Laugier & Dumon 2004)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: A recipe serves 4 people and calls for 2 cups of flour. You need to serve 6. Proportional reasoning: 2/4 = x/6, so x = 3 cups. The identical cognitive move, applied to chemistry: a reaction requires 2 mol NaOH per 1 mol H2SO4. You have 0.5 mol H2SO4. How much NaOH? 2/1 = x/0.5, so x = 1.0 mol NaOH. Same reasoning, different context.

- PRIM-SCL006: **Unit analysis**
  - Reasoning move: Given a calculation involving physical quantities, use dimensional analysis (tracking units through every step) to verify correctness, convert between unit systems, and catch errors before they propagate.
  - Description: The cognitive operation of treating units as algebraic objects that must balance on both sides of an equation. If you are calculating mass and your answer comes out in liters, something is wrong -- unit analysis catches it. This is the single most reliable error-detection tool in quantitative science. Unit analysis also provides a constructive problem-solving strategy: if you know the starting units and the target units, you can chain conversion factors to build the solution path even when the conceptual route is unclear. This primitive has no intra-domain dependencies because it is a foundational quantitative skill that does not require the mole concept or any chemical knowledge -- it applies to any quantitative reasoning.
  - Semi-formal: For any calculation: units(left side) = units(right side). Conversion: quantity_target = quantity_source x (unit_target / unit_source) where the conversion factor has the value 1 (e.g., 1 kg / 1000 g = 1). Multi-step: chain conversion factors so that intermediate units cancel. If final units do not match the expected quantity type (mass, volume, energy, etc.), the calculation contains an error.
  - Depends: none (foundational quantitative skill -- no chemical content required)
  - Ownership: SCL
  - Source: SRC-SCL001 (Arons 1997, dimensional analysis), SRC-GLB008 (OpenStax Ch. 1)
  - Referenced by: --
  - Tier: C
  - Real-world hook: A European recipe calls for 200 mL of milk. Your measuring cup is in cups. Unit analysis: 200 mL x (1 cup / 236.6 mL) = 0.85 cups. In a medical context: a medication dose is 5 mg/kg body weight. You weigh 70 kg. Unit analysis: 5 mg/kg x 70 kg = 350 mg. The units guide the calculation and verify the answer.

## 4. Definitions

- DEF-SCL001: **Molarity**
  - Reasoning move: Given a solution preparation scenario, calculate the number of moles of solute per liter of solution (molarity, M) to express concentration in chemistry's standard unit for reaction stoichiometry and laboratory work.
  - Description: Molarity is the standard concentration unit in chemistry: M = mol solute / L solution. It combines the mole concept (PRIM-SCL002, converting between particles and measurable amounts) with concentration reasoning (PRIM-SCL003, amount per volume determines effect). Molarity is the unit that connects a balanced equation (which speaks in moles) to a volumetric measurement (which uses liters). When a protocol says "add 100 mL of 0.1 M HCl," molarity tells you exactly how many moles of HCl that delivers: 0.1 mol/L x 0.100 L = 0.01 mol. Molarity is a definition, not a primitive, because it is built from two prior reasoning moves (mole concept + concentration) and introduces no new cognitive operation -- it names a specific, conventional way of measuring concentration.
  - Semi-formal: Molarity M = n / V, where n = moles of solute and V = volume of solution in liters. Units: mol/L, abbreviated M. For dilution: M_1 V_1 = M_2 V_2. For stoichiometric use: moles of solute = M x V(in liters).
  - Depends: PRIM-SCL002 (mole concept -- moles in the numerator), PRIM-SCL003 (concentration reasoning -- amount per volume)
  - Ownership: SCL
  - Source: SRC-GLB008 (OpenStax Ch. 4), SRC-GLB009 (Zumdahl Ch. 4)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: A home pool test kit measures chlorine concentration in ppm, but the chemistry behind water treatment uses molarity. When a municipal water plant adds sodium hypochlorite solution, the engineers calculate molarity to determine how many liters of concentrated stock to dilute into the treatment tank. Similarly, a pharmacist calculating IV drip rates uses molarity to ensure the correct dose per hour.

- DEF-SCL002: **Parts per million/billion (ppm/ppb)**
  - Reasoning move: Given a trace-level concentration scenario (pollution, contaminants, micronutrients), express concentration in parts per million (mg/L in water) or parts per billion (micrograms/L in water) to reason about quantities too small for molarity to be intuitive.
  - Description: Parts per million (ppm) and parts per billion (ppb) are concentration units designed for very dilute solutions and trace contaminants. 1 ppm in water is approximately 1 mg/L; 1 ppb is approximately 1 microgram/L. These units are essential for environmental chemistry (pollution limits are always in ppm or ppb), toxicology (LD50 values, exposure limits), and water quality (EPA drinking water standards). PPM/PPB is a definition, not a primitive, because it is a specialized application of concentration reasoning (PRIM-SCL003) for the trace-concentration regime. The reasoning move is the same -- amount per volume determines effect -- but the unit choice communicates "this is a very small amount" and enables comparison against regulatory thresholds.
  - Semi-formal: For aqueous solutions (density approximately 1 g/mL): 1 ppm = 1 mg solute / 1 L solution = 1 mg/kg. 1 ppb = 1 microgram solute / 1 L solution = 1 microgram/kg. Conversion: 1 ppm = 1000 ppb. Comparison against regulatory threshold T: if c > T, the sample exceeds the standard.
  - Depends: PRIM-SCL003 (concentration reasoning -- ppm/ppb are concentration units for the trace regime)
  - Ownership: SCL
  - Source: SRC-GLB008 (OpenStax Ch. 4), SRC-GLB010 (ACS Chemistry in Context, Ch. 5)
  - Referenced by: --
  - Tier: C
  - Real-world hook: The EPA's maximum contaminant level for arsenic in drinking water is 10 ppb. A community well tests at 14 ppb. Without ppm/ppb reasoning, you cannot evaluate whether this exceeds the standard. With it, you know: 14 > 10, so the well fails. Converting: 14 ppb = 0.014 ppm = 0.014 mg/L -- a vanishingly small amount that is nonetheless biologically significant over years of exposure.

- DEF-SCL003: **Ideal gas reasoning**
  - Reasoning move: Given a gas sample, use PV = nRT to relate pressure, volume, temperature, and mole count -- predicting how changing one variable affects the others under the assumption that gas particles do not interact.
  - Description: The ideal gas law (PV = nRT) is the paradigmatic scale-bridging equation in chemistry: it connects a molecular-level quantity (n, moles of gas particles) to three macroscopic, measurable quantities (P, V, T). The "ideal" assumption is that gas particles have negligible volume and no intermolecular forces -- which is approximately true for most gases at moderate temperatures and pressures. Ideal gas reasoning is a definition rather than a primitive because it combines the mole concept (PRIM-SCL002, converting between particles and measurable amounts) and unit analysis (PRIM-SCL006, ensuring P, V, n, T, and R have consistent units) into a specific quantitative relationship. It introduces no new cognitive operation beyond those two primitives plus the empirical relationship PV = nRT itself.
  - Semi-formal: PV = nRT, where P = pressure (atm or kPa), V = volume (L), n = moles of gas, R = gas constant (0.08206 L-atm/mol-K or 8.314 J/mol-K), T = temperature in Kelvin. Qualitative predictions: at constant T and n, increasing P decreases V (Boyle). At constant P and n, increasing T increases V (Charles). At constant T and V, increasing n increases P.
  - Depends: PRIM-SCL002 (mole concept -- n in the equation), PRIM-SCL006 (unit analysis -- units must be consistent across P, V, n, R, T)
  - Ownership: SCL
  - Source: SRC-GLB008 (OpenStax Ch. 9), SRC-GLB009 (Zumdahl Ch. 5)
  - Referenced by: --
  - Tier: E
  - Real-world hook: Why does a basketball go flat in cold weather? Ideal gas reasoning: at constant n and approximately constant V (the ball is somewhat rigid), decreasing T decreases P. The gas inside exerts less pressure, so the ball feels deflated. Conversely, a sealed bag of chips puffs up on an airplane because the cabin pressure (P external) drops while the gas inside still has the same n and T.

- DEF-SCL004: **Colligative properties**
  - Reasoning move: Given a solution with dissolved particles, predict changes in boiling point, freezing point, vapor pressure, or osmotic pressure based on the NUMBER of dissolved particles, regardless of their chemical identity.
  - Description: Colligative properties are the quintessential emergent-scale phenomenon: they depend on how MANY particles are dissolved, not on WHAT those particles are. Dissolving any substance in water raises the boiling point and lowers the freezing point by an amount proportional to the concentration of dissolved particles. This is why salt on icy roads works (lowers freezing point) and why adding antifreeze to a car radiator prevents both freezing and boiling over. Colligative property reasoning combines the mole concept (PRIM-SCL002, counting particles) with emergent property reasoning (PRIM-SCL004, the bulk property arises from collective behavior, not individual molecular identity). It is Enrichment because it builds on two Core primitives in a specialized way that, while pedagogically valuable, is not required by any downstream Core item.
  - Semi-formal: For a solution with solute particle concentration c (in mol/L or molality): delta-T_b = K_b x m x i (boiling point elevation), delta-T_f = K_f x m x i (freezing point depression), where m = molality, K_b and K_f are solvent-specific constants, and i = van't Hoff factor (number of particles per formula unit; i = 1 for molecular solutes, i = 2 for NaCl, i = 3 for CaCl2). The key insight: identity of solute does not matter; only the count i x m matters.
  - Depends: PRIM-SCL002 (mole concept -- counting dissolved particles), PRIM-SCL004 (emergent property reasoning -- colligative properties are the paradigm case of emergence)
  - Ownership: SCL
  - Source: SRC-GLB008 (OpenStax Ch. 11), SRC-GLB009 (Zumdahl Ch. 11)
  - Referenced by: --
  - Tier: E
  - Real-world hook: In winter, road crews spread salt (NaCl) on icy roads. Colligative property reasoning explains why: each formula unit of NaCl dissociates into 2 particles (Na+ and Cl-), doubling the freezing-point depression per mole compared to a molecular solute like sugar. That is why salt works better than sugar for de-icing, even though both dissolve in water.

- DEF-SCL005: **Safety and risk reasoning**
  - Reasoning move: Given a substance with its hazard information (GHS pictograms, LD50 value, permissible exposure limit, exposure route, and duration), assess the risk to a person by combining the substance's inherent hazard with the concentration, exposure route, and duration of exposure.
  - Description: The cognitive operation of separating HAZARD (an intrinsic property of the substance -- how toxic, flammable, or corrosive it is) from RISK (the probability and severity of actual harm, which depends on concentration, route, and duration). A bottle of concentrated hydrochloric acid is hazardous. But 0.1 M HCl in a controlled lab setting with gloves and goggles is low risk. Conversely, even "safe" substances become dangerous at extreme concentrations (drinking too much water can cause hyponatremia). Safety reasoning integrates concentration reasoning (PRIM-SCL003) with hazard data to produce a risk assessment. This is a definition rather than a primitive because it combines concentration reasoning with externally provided hazard data -- it does not introduce a new cognitive operation but rather a specific, critical application of concentration reasoning to human safety.
  - Semi-formal: Risk = f(Hazard, Concentration, Route, Duration). Hazard is intrinsic: LD50 (dose lethal to 50% of test animals, in mg/kg body weight), GHS category (1 = most hazardous). Concentration is extrinsic: actual exposure level in ppm, mg/m^3, or mg/kg. Route matters: ingestion, inhalation, and dermal absorption have different thresholds for the same substance. Duration matters: acute (single exposure) vs. chronic (repeated low-level exposure) have different risk profiles. Risk is LOW when concentration << threshold for the given route and duration; HIGH when concentration >= threshold.
  - Depends: PRIM-SCL003 (concentration reasoning -- risk assessment requires knowing the concentration of exposure)
  - Ownership: SCL
  - Source: SRC-GLB008 (OpenStax Ch. 18, environmental chemistry), SRC-GLB010 (ACS Chemistry in Context, Ch. 1--2)
  - Referenced by: --
  - Tier: C
  - Real-world hook: A Safety Data Sheet (SDS) for acetone lists: LD50 (oral, rat) = 5800 mg/kg; GHS pictogram: flammable, irritant; permissible exposure limit (PEL) = 1000 ppm (8-hour TWA). Safety reasoning: at the concentrations encountered when removing nail polish in a ventilated room, the risk is low. But using acetone in a closed, unventilated space for hours could approach the PEL -- same substance, different risk because the concentration and duration changed.

## 5. Contested Concepts

The primary contested boundaries for SCL are with STR and NRG, but they are cleanly resolved:

| Concept | SCL Version (Owner) | Other Domain Version (If Any) | Resolution |
|---------|---------------------|-------------------------------|------------|
| Boiling point | SCL owns the macro-level phenomenon: boiling point as an emergent property of 10^23 molecules (PRIM-SCL004) and its dependence on particle count (DEF-SCL004) | STR owns the molecular-level explanation: intermolecular force hierarchy determines WHICH substance has higher boiling point (PRIM-STR004, DEF-STR006) | Boundary principle P3: bridging to bulk = SCL. Molecular-level mechanism = STR. Connected via CP-001 (Structure-to-Bulk-Property Bridge). |
| Measurement and units | SCL owns unit analysis and dimensional reasoning (PRIM-SCL006) | NRG uses units like joules and calories (DEF-NRG005) | Boundary principle P5: measurement and unit reasoning = SCL. The energy concepts themselves = NRG. NRG defines what energy IS; SCL handles how to convert and verify units. |
| Molar mass | SCL owns the mole concept and the moles-to-grams conversion (PRIM-SCL002) | COM owns the formula from which molar mass is calculated (PRIM-COM005) | Clean split: COM provides the formula (what atoms, how many); SCL provides the moles-to-grams bridge (how to weigh it out). |

No contested concepts exist between SCL and CHG. CHG's items are about what transforms, how fast, and how far. SCL's items are about translating molecular counts to macroscopic quantities.

## 6. Real-World Hooks

| ID | Concept | Everyday Application |
|----|---------|---------------------|
| PRIM-SCL001 | Macro-to-submicro translation | Explaining why rubbing alcohol feels cold on skin (evaporation at the molecular level absorbs energy from skin) |
| PRIM-SCL002 | Mole concept | Understanding that a "serving" on a nutrition label is a macroscopic proxy for a molecular count -- 18 g of water is 1 mole (6 x 10^23 molecules) |
| PRIM-SCL003 | Concentration reasoning | Reading a water quality report: "chlorine residual: 1.5 ppm" -- is that safe? (EPA allows up to 4 ppm) |
| PRIM-SCL004 | Emergent property reasoning | Explaining why gold nanoparticles are red (not gold-colored) -- color is an emergent property that changes with particle size |
| PRIM-SCL005 | Proportional reasoning | Doubling a cookie recipe: if 2 cups flour serves 24 cookies, 4 cups serves 48 -- same proportional reasoning used in stoichiometry |
| PRIM-SCL006 | Unit analysis | Converting a European recipe from grams and Celsius to cups and Fahrenheit using dimensional analysis |
| DEF-SCL001 | Molarity | Understanding why a pharmacist dilutes a stock solution to a specific molarity for an IV drip |
| DEF-SCL002 | Parts per million/billion | Evaluating a news report: "PFAS detected at 70 ppt in drinking water" -- is that a lot? (EPA advisory level is 70 ppt) |
| DEF-SCL003 | Ideal gas reasoning | Understanding why a tire pressure warning light comes on in cold weather (gas pressure drops with temperature) |
| DEF-SCL004 | Colligative properties | Explaining why adding salt to pasta water raises the boiling point (and why the effect is too small to matter for cooking) |
| DEF-SCL005 | Safety and risk reasoning | Reading a Safety Data Sheet before using a cleaning product and determining whether ventilation is needed based on exposure limits |

## 7. Intra-Domain Dependency Graph

```
PRIM-SCL006 (Unit analysis)            PRIM-SCL001 (Macro-to-submicro translation)
[no intra-domain deps]                       |
                                             +---> PRIM-SCL002 (Mole concept)
                                             |          |
                                             |          +---> PRIM-SCL003 (Concentration reasoning)
                                             |          |          |
                                             |          |          +---> DEF-SCL001 (Molarity)
                                             |          |          +---> DEF-SCL002 (Parts per million/billion)
                                             |          |          +---> DEF-SCL005 (Safety and risk reasoning)
                                             |          |
                                             |          +---> PRIM-SCL005 (Proportional reasoning)
                                             |          |
                                             |          +---> DEF-SCL003 (Ideal gas reasoning)
                                             |          |          [also depends on PRIM-SCL006]
                                             |          |
                                             |          +---> DEF-SCL004 (Colligative properties)
                                             |                     [also depends on PRIM-SCL004]
                                             |
                                             +---> PRIM-SCL004 (Emergent property reasoning)
```

**Acyclicity verification**: All arrows point from items with lower dependency depth to items with higher dependency depth. PRIM-SCL006 and PRIM-SCL001 are roots (no intra-domain dependencies). PRIM-SCL002 depends on PRIM-SCL001 (and PRIM-COM005 imported). PRIM-SCL003, PRIM-SCL004, and PRIM-SCL005 depend on PRIM-SCL002 or PRIM-SCL001. All DEFs depend on previously listed PRIMs. DEF-SCL003 has a cross-branch dependency on PRIM-SCL006 (a root), which does not create a cycle. DEF-SCL004 has a cross-branch dependency on PRIM-SCL004 (depth 1), which does not create a cycle. The graph is a DAG.

## 8. Cross-Domain Interface

### Exports

| ID | Concept | Imported by |
|----|---------|-------------|
| PRIM-SCL001 | Macro-to-submicro translation | -- |
| PRIM-SCL002 | Mole concept | CHG |
| PRIM-SCL003 | Concentration reasoning | CHG |
| PRIM-SCL004 | Emergent property reasoning | -- |
| PRIM-SCL005 | Proportional reasoning | CHG |
| PRIM-SCL006 | Unit analysis | -- |
| DEF-SCL001 | Molarity | CHG |
| DEF-SCL002 | Parts per million/billion | -- |
| DEF-SCL003 | Ideal gas reasoning | -- |
| DEF-SCL004 | Colligative properties | -- |
| DEF-SCL005 | Safety and risk reasoning | -- |

### Imports

| ID | Concept | Imported from | Used by |
|----|---------|---------------|---------|
| PRIM-COM001 | Atomic composition analysis | COM | PRIM-SCL001 |
| PRIM-COM005 | Chemical formula reading | COM | PRIM-SCL002 |
| PRIM-COM008 | Causal chain reasoning | COM | General meta-reasoning deployed throughout SCL |

## 9. Difficulty Tiers

| ID | Concept | Tier | Justification |
|----|---------|------|---------------|
| PRIM-SCL001 | Macro-to-submicro translation | C | Foundational: the defining cognitive operation of scale reasoning; without it, students cannot bridge between levels |
| PRIM-SCL002 | Mole concept | C | Essential quantitative bridge: no mole concept means no connection between equations and lab measurements; CHG depends on this |
| PRIM-SCL003 | Concentration reasoning | C | Essential for interpreting any real-world chemical claim involving solutions, pollution, medication, or exposure; CHG depends on this |
| PRIM-SCL004 | Emergent property reasoning | C | Conceptually critical: the "centralized to decentralized" threshold; without it, students misattribute bulk properties to single molecules |
| PRIM-SCL005 | Proportional reasoning | C | Quantitative workhorse: stoichiometry, dilution, and unit conversion all deploy this reasoning move; CHG depends on this |
| PRIM-SCL006 | Unit analysis | C | Universal error-detection tool: the single most reliable way to verify quantitative calculations; used throughout all quantitative reasoning |
| DEF-SCL001 | Molarity | C | Standard concentration unit: needed for all solution-based stoichiometry and laboratory work in CHG; CHG depends on this |
| DEF-SCL002 | Parts per million/billion | C | Essential for environmental and toxicological literacy: pollution limits, water quality, and exposure standards are universally reported in ppm/ppb |
| DEF-SCL003 | Ideal gas reasoning | E | Enrichment: valuable for understanding everyday gas behavior but not required by any Core item in SCL or other domains |
| DEF-SCL004 | Colligative properties | E | Enrichment: elegant demonstration of emergence but not required by any Core item; omitting it does not break any dependency chain |
| DEF-SCL005 | Safety and risk reasoning | C | Essential for chemical literacy: every non-major should be able to read an SDS and assess whether an exposure is dangerous |

**Tier constraint verification**: No Enrichment item is a prerequisite for any Core item. DEF-SCL003 (E) depends only on PRIM-SCL002 (C) and PRIM-SCL006 (C); nothing depends on DEF-SCL003. DEF-SCL004 (E) depends only on PRIM-SCL002 (C) and PRIM-SCL004 (C); nothing depends on DEF-SCL004. The Core tier alone (9 items: 6 PRIM + DEF-SCL001 + DEF-SCL002 + DEF-SCL005) forms a self-contained, dependency-complete sub-taxonomy.

## 10. Self-Audit Checklist

- [x] Every PRIM has: reasoning move formulation ("Given X, do Y to determine Z"), description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [x] Every DEF depends only on previously listed PRIM/DEF (check intra-domain dependency graph)
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in the source domain's exports (verified: PRIM-COM001, PRIM-COM005, and PRIM-COM008 are all in COM's export table in DOMAIN-COM.md Section 8)
- [x] Dissolution argument is present and non-trivial (5 sentences explaining why SCL is distinct from COM, STR, NRG, and CHG, with reference to Johnstone's triplet model)
- [x] Real-world hooks cover everyday non-major contexts (water quality reports, medication dosages, pollution levels, cooking measurements, safety data sheets, pool chemistry, tire pressure, road salt, nutrition labels, nail polish remover)
- [x] Intra-domain dependency graph is acyclic (verified: two root nodes PRIM-SCL001 and PRIM-SCL006; all edges point from shallower to deeper dependency depth; no cycles)
- [x] Tier annotations (C/E) are present on all 11 items (9 Core, 2 Enrichment)
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry in CONVENTIONS.md Section 9: no overlap with COM, STR, NRG, or CHG items)
- [x] Reasoning moves are genuinely "Given X, do Y" cognitive operations (not mere topic labels or vocabulary words)
