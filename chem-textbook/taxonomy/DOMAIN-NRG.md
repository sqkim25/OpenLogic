# DOMAIN-NRG v0.1

## 0. Sources & Assumptions

- SRC-NRG001: Bain et al., "College students' understanding of enthalpy and Hess's law," *J. Chem. Educ.*, 2014 (misconceptions about energy storage and bond breaking/forming)
- SRC-NRG002: Lambert, "Disorder -- A cracked crutch for supporting entropy discussions," *J. Chem. Educ.*, 2002 (why "disorder" framing for entropy is misleading; supports probability framing)
- SRC-NRG003: Granville, "Students' misconceptions in learning chemistry," *J. Chem. Educ.*, 1985 (enduring confusion between heat and temperature)
- SRC-GLB008: OpenStax, *Chemistry 2e*, 2019, Ch. 5 (thermochemistry), Ch. 12 (thermodynamics)
- SRC-GLB009: Zumdahl & Zumdahl, *Chemistry*, 10th ed., 2017, Ch. 6 (thermochemistry), Ch. 16 (spontaneity, entropy, free energy)
- ASM-NRG001: Energy reasoning is taught qualitatively: energy diagrams, exo/endo classification, and entropy as probability. No thermodynamic equations beyond delta-H = negative (exo) / positive (endo). Justification: non-majors need the conceptual reasoning moves (is this favorable? which direction does energy flow?) but not the quantitative apparatus (Hess's law, calorimetry calculations, delta-G = delta-H - T*delta-S). Quantitative energy calculations are a majors-track skill (SRC-NRG001).
- ASM-NRG002: Entropy is framed EXCLUSIVELY as probability of arrangements, NEVER as "disorder." Justification: CER shows the disorder metaphor is actively misleading -- students apply it to spatial messiness rather than microstates (SRC-NRG002). The probability framing (more arrangements = more probable = higher entropy) is conceptually accurate, accessible, and transferable.

## 1. Domain Intent

- **Governing question**: What determines whether a process will occur and in which direction?
- **Scope**: Tracking energy through processes (conservation), comparing bond energies, classifying processes as exo- or endothermic, reasoning about entropy (dispersal of energy and matter), predicting spontaneity, and identifying activation energy barriers. NRG provides the favorability layer: whether a process is energetically and entropically favorable, and what barriers must be overcome.
- **Non-goals**: What substances are or what atoms they contain (COM). How atoms are arranged in three dimensions or what intermolecular forces exist (STR). What specific products form, how fast a reaction proceeds, or how equilibrium behaves dynamically (CHG). How to bridge molecular-level energy descriptions to macroscopic measurements like moles or concentration (SCL).
- **Dissolution argument**: Energy reasoning cannot merge into structure -- two differently-structured molecules may store the same energy. A straight-chain and branched isomer of the same formula can have nearly identical total bond energies despite different 3D arrangements. Energy tells you WHETHER a process is favorable; it does not tell you WHAT the products are (CHG) or HOW the molecules are shaped (STR). Conversely, knowing a molecule's shape tells you nothing about whether its formation was exothermic. You can teach conservation, entropy, and spontaneity without ever specifying a particular reaction mechanism, a particular molecular geometry, or a particular macroscopic measurement. The energy domain is the "accounting department" of chemistry: it tracks debits and credits without needing to know the physical layout of the office (STR) or the specific business transactions (CHG).
- **Threshold schema mapping**: Deterministic --> Probabilistic. The foundational conceptual shift in NRG is recognizing that entropy -- and therefore spontaneity -- is governed by probability, not by deterministic "energy always decreases" reasoning. Students who fail to cross this threshold believe that only exothermic processes are spontaneous, missing the entropic contribution entirely. The threshold is crossed when students understand that an endothermic process can be spontaneous if entropy increase is large enough (e.g., ice melting at room temperature).

## 2. Prerequisites

NRG depends on COM and imports the following:

| DEP ID | Imported Item | Reason |
|--------|---------------|--------|
| DEP-NRG001 | PRIM-COM001 (Atomic composition analysis) | Energy tracking requires knowing what atoms and bonds are present in a system; you must identify the constituents before you can track energy through them |
| DEP-NRG002 | PRIM-COM006 (Conservation of atoms) | Energy conservation reasoning parallels atom conservation: just as atoms are neither created nor destroyed, energy is neither created nor destroyed. The conservation pattern from COM provides the conceptual scaffold for energy conservation |

NRG does NOT depend on STR, CHG, or SCL. Independence arguments (from CONVENTIONS.md Section 10):
- **NRG does not depend on STR**: Energy conservation, entropy, spontaneity, and activation energy are abstract energy-accounting reasoning moves. Bond energy reasoning (PRIM-NRG002) reasons about energy stored in bonds without needing bond angles, molecular shape, or intermolecular force hierarchies.
- **NRG does not depend on CHG**: NRG defines whether a process is favorable; CHG defines what transforms and how fast. You can classify a process as exothermic without knowing its balanced equation or reaction type.
- **NRG does not depend on SCL**: Energy concepts are defined qualitatively at the conceptual level, not in terms of moles, molarity, or macroscopic measurement. Specific heat capacity (DEF-NRG002) is defined as an energy-per-mass-per-degree concept within NRG; SCL handles its deployment in quantitative calculations.

## 3. Primitives

- PRIM-NRG001: **Energy tracking**
  - Reasoning move: Given a process (chemical reaction, physical change, or energy transfer), trace energy through the system: identify input energy forms, energy transformations within the system, and output energy forms, then verify that total energy is conserved.
  - Description: The cognitive operation of following energy through a process the way an accountant follows money through transactions. Every process involves energy entering in some form (chemical, thermal, light, electrical, mechanical), being stored or converted within the system, and leaving in some form. The total energy in equals the total energy out -- this is the first law of thermodynamics stated as a reasoning move. Energy tracking is the foundational energy primitive: before you can classify a process as exo- or endothermic, reason about entropy, or assess spontaneity, you must first be able to trace where energy comes from, where it goes, and verify the books balance.
  - Semi-formal: For any process P in system S: E_in(P) = E_stored(P) + E_out(P). Energy forms include chemical (stored in bonds), thermal (kinetic energy of particles), radiant (light), electrical, and mechanical. Conservation requires sum of all E_in = sum of all E_out when delta-E_stored is accounted for. No energy is created or destroyed.
  - Depends: PRIM-COM001 (atomic composition analysis -- must identify what substances and bonds are present to trace energy through them)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Ch. 5, Section 5.1), SRC-GLB009 (Zumdahl Ch. 6, Section 6.1)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: When you eat a granola bar before a run, you are performing energy tracking: chemical energy stored in food bonds is converted to thermal energy (body heat) and mechanical energy (muscle movement). The total energy from the granola bar equals the heat you radiate plus the work your muscles do. Nothing is lost -- just transformed.

- PRIM-NRG002: **Bond energy reasoning**
  - Reasoning move: Given a chemical reaction, compare the total energy required to break all bonds in the reactants with the total energy released when forming all bonds in the products, then determine whether the reaction is a net energy producer or consumer.
  - Description: The cognitive operation of using bond energies to predict the net energy flow of a reaction. Breaking bonds ALWAYS requires energy input (endothermic step); forming bonds ALWAYS releases energy (exothermic step). The net result depends on which set of bonds is stronger: if product bonds are stronger (more energy released forming them) than reactant bonds (less energy needed to break them), the reaction is exothermic overall. This primitive corrects a pervasive misconception: students often believe breaking bonds releases energy. The correct reasoning is that bonds are energy-storing structures -- breaking them costs energy; making them pays out.
  - Semi-formal: For reaction R --> P: Energy_required = sum of bond energies broken in R. Energy_released = sum of bond energies formed in P. Net energy = Energy_required - Energy_released. If net > 0, the reaction is endothermic (absorbed energy). If net < 0, the reaction is exothermic (released energy). Note: this is an approximation; exact values depend on specific bond environments.
  - Depends: PRIM-NRG001 (energy tracking -- bond energy reasoning is a specific application of energy conservation to chemical bonds)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Ch. 5, Section 5.4), SRC-GLB009 (Zumdahl Ch. 6, Section 6.4), SRC-NRG001 (Bain et al. 2014, bond energy misconceptions)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: Natural gas (methane, CH4) burns in your stove. Breaking the C-H bonds in methane and the O=O bonds in oxygen requires energy, but forming the C=O bonds in CO2 and O-H bonds in H2O releases MORE energy. The net surplus heats your food. Bond energy reasoning explains why some fuels are better than others: they have weaker bonds to break and form stronger bonds in the products.

- PRIM-NRG003: **Exo/endothermic classification**
  - Reasoning move: Given an energy diagram or description of a process, classify it as exothermic (energy released to surroundings) or endothermic (energy absorbed from surroundings) to predict temperature changes and energy flow direction.
  - Description: The cognitive operation of determining whether a chemical or physical process releases or absorbs energy. This is the foundational binary classification in energy reasoning: every process that involves energy change is either exo- or endothermic. The classification depends on comparing energy of reactants vs. products, not on the speed or mechanism of the process. Exothermic processes raise the temperature of the surroundings; endothermic processes lower it. This classification is about direction of energy flow, not about whether the process is spontaneous (that requires entropy reasoning as well).
  - Semi-formal: Given a process P with initial state energy E_i and final state energy E_f: if E_f < E_i, then P is exothermic (delta-E < 0, energy released to surroundings). If E_f > E_i, then P is endothermic (delta-E > 0, energy absorbed from surroundings). If E_f = E_i, then P is thermoneutral (no net energy transfer).
  - Depends: PRIM-NRG001 (energy tracking -- must trace energy flow to determine direction)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Ch. 5, Section 5.2), SRC-GLB009 (Zumdahl Ch. 6, Section 6.1)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: When you hold an instant cold pack (endothermic dissolution of ammonium nitrate) or feel warmth from a hand warmer (exothermic oxidation of iron), you are experiencing the macroscopic consequence of exo/endothermic classification. The cold pack absorbs energy from your hand; the hand warmer releases it.

- PRIM-NRG004: **Entropy reasoning**
  - Reasoning move: Given a before-and-after description of a process, determine whether the number of possible arrangements (microstates) of energy and matter increased or decreased, and thereby whether the change is entropically favored (more arrangements) or disfavored (fewer arrangements).
  - Description: The cognitive operation of assessing entropy change as a probability judgment. Entropy is a measure of how many different ways the particles and energy in a system can be arranged. A state with more possible arrangements is more probable and therefore has higher entropy. This is NOT about "disorder" -- that framing is misleading (SRC-NRG002). Instead, think of entropy the way you think about shuffling a deck of cards: there are astronomically more ways to have a shuffled deck than an ordered one, so shuffling is overwhelmingly probable. Key entropy-increasing signatures: solid dissolving into solution (particles spread out), gas expanding into a larger volume (more positions available), one substance breaking into many pieces (more independent particles), temperature increasing (more energy arrangements). Entropy reasoning is the second pillar of favorability alongside energy reasoning.
  - Semi-formal: For a process transforming state S_1 to state S_2: let W_1 = number of microstates in S_1 and W_2 = number of microstates in S_2. If W_2 > W_1, entropy increases (delta-S > 0, entropically favored). If W_2 < W_1, entropy decreases (delta-S < 0, entropically disfavored). Qualitative predictors: more particles --> higher entropy; gas > liquid > solid; higher temperature --> higher entropy; larger volume --> higher entropy.
  - Depends: none within NRG (foundational energy concept -- entropy is an independent pillar alongside energy conservation)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Ch. 12, Section 12.2), SRC-GLB009 (Zumdahl Ch. 16, Section 16.1), SRC-NRG002 (Lambert 2002, probability framing of entropy)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: Why does an ice cube melt on your kitchen counter? The water molecules in ice are locked in a rigid crystal with very few arrangements. Liquid water has enormously more possible arrangements. Melting is overwhelmingly probable -- like shuffling a sorted deck. That is entropy reasoning: more arrangements = more probable = favored direction.

- PRIM-NRG005: **Spontaneity reasoning**
  - Reasoning move: Given the energy change (exo/endo) AND entropy change (increase/decrease) of a process, determine whether the process will occur without continuous external energy input (spontaneous) or whether it requires sustained external driving (non-spontaneous).
  - Description: The cognitive operation of combining the two pillars of favorability -- energy and entropy -- to predict whether a process happens on its own. Spontaneous does NOT mean fast (a diamond converting to graphite is spontaneous but imperceptibly slow). It means thermodynamically favorable overall. Four cases arise: (1) exothermic + entropy increase = always spontaneous; (2) endothermic + entropy decrease = never spontaneous; (3) exothermic + entropy decrease = spontaneous at low temperature; (4) endothermic + entropy increase = spontaneous at high temperature. Cases 3 and 4 are temperature-dependent because temperature determines how much the entropy term matters relative to the energy term. This is presented qualitatively, NOT through the delta-G equation.
  - Semi-formal: A process is spontaneous if the combined effect of energy favorability and entropy favorability is net favorable. Let delta-H represent energy change direction (neg = exo, pos = endo) and delta-S represent entropy change direction (pos = increase, neg = decrease). Spontaneous when: (delta-H < 0 AND delta-S > 0) always; (delta-H < 0 AND delta-S < 0) at low T; (delta-H > 0 AND delta-S > 0) at high T; (delta-H > 0 AND delta-S < 0) never.
  - Depends: PRIM-NRG003 (exo/endothermic classification -- need to know energy direction), PRIM-NRG004 (entropy reasoning -- need to know entropy direction)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Ch. 12, Section 12.4), SRC-GLB009 (Zumdahl Ch. 16, Section 16.4)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: Water freezing on a cold winter night is exothermic (energy released to surroundings) but entropy-decreasing (liquid to solid = fewer arrangements). It is spontaneous at low temperature because the energy favorability outweighs the entropy penalty. On a warm spring day, the reverse happens: melting is endothermic but entropy-increasing, and it becomes spontaneous because the entropy favorability outweighs the energy penalty. Temperature is the referee between energy and entropy.

- PRIM-NRG006: **Activation energy reasoning**
  - Reasoning move: Given a process that is thermodynamically favorable (spontaneous) but does not seem to occur, identify the activation energy barrier that must be overcome to initiate the process, and explain how catalysts or increased temperature can lower or overcome this barrier.
  - Description: The cognitive operation of recognizing that spontaneity alone does not guarantee that a process will proceed at an observable rate. Activation energy is the minimum energy input required to get a reaction started -- like the push needed to roll a boulder over a hill before it can roll downhill on its own. Even if the products are lower in energy than the reactants (exothermic), the reactants must first reach a high-energy transition state. Catalysts provide an alternative pathway with a lower activation energy; increased temperature gives more particles enough kinetic energy to clear the barrier. This primitive explains why gasoline does not spontaneously combust at room temperature despite being thermodynamically favorable: the activation energy barrier prevents it until a spark provides the initial push.
  - Semi-formal: For a spontaneous reaction R --> P with delta-E < 0: there exists an activation energy E_a > 0 such that reactants must reach energy E_i + E_a (the transition state) before proceeding to products at E_f. Rate of reaction increases when: (a) E_a is lowered (catalyst provides alternative pathway with lower E_a), or (b) temperature increases (more particles have kinetic energy >= E_a). A catalyst changes E_a but NOT delta-E (the net energy change is unchanged).
  - Depends: PRIM-NRG001 (energy tracking -- activation energy is an energy concept requiring energy accounting)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Ch. 12, Section 12.7), SRC-GLB009 (Zumdahl Ch. 12, Section 12.7)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: A match head is coated with chemicals whose combustion is highly exothermic (spontaneous), but they sit safely in a box indefinitely. Striking the match provides friction (thermal energy) that overcomes the activation energy barrier. Your car's catalytic converter lowers the activation energy for converting toxic exhaust gases (CO, NOx) into less harmful products (CO2, N2) -- the reaction is spontaneous but too slow without the catalyst.

## 4. Definitions

- DEF-NRG001: **Heat vs temperature**
  - Reasoning move: Given two objects at different temperatures in contact, distinguish heat (the energy transferred between them) from temperature (the average molecular kinetic energy of each), and predict the direction of heat flow (hot to cold) and the eventual equilibrium.
  - Description: Heat and temperature are the most commonly conflated concepts in introductory chemistry (SRC-NRG003). Temperature is a property of a single object -- it measures how fast, on average, the molecules in that object are moving. Heat is not a property of an object but a process: it is the transfer of thermal energy from a higher-temperature object to a lower-temperature one. A bathtub of lukewarm water contains more thermal energy (and can transfer more heat) than a thimble of boiling water, even though the thimble is at a higher temperature. This definition provides the vocabulary for precise energy reasoning: PRIM-NRG001 tracks energy; DEF-NRG001 specifies what "thermal energy transfer" means.
  - Semi-formal: Temperature T of object X = average kinetic energy of particles in X. Heat q = energy transferred between objects due to temperature difference. Heat flows from high-T object to low-T object until T_1 = T_2 (thermal equilibrium). Heat is measured in joules (or calories); temperature is measured in degrees (Celsius, Kelvin). Adding heat to an object raises its temperature by an amount that depends on its mass and specific heat capacity.
  - Depends: PRIM-NRG001 (energy tracking -- heat is a specific form of energy transfer, requiring the general energy tracking framework)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Ch. 5, Section 5.1), SRC-GLB009 (Zumdahl Ch. 6, Section 6.1), SRC-NRG003 (Granville 1985, heat/temperature confusion)
  - Referenced by: SCL
  - Tier: C
  - Real-world hook: When you check a child's forehead for fever, you are sensing temperature (average molecular kinetic energy). When you run a hot bath to soothe sore muscles, you are using heat transfer -- thermal energy flows from the hot water into your cooler body until both reach the same temperature. The bath "feels hot" because heat is flowing into you, not because the water has some substance called "heat" inside it.

- DEF-NRG002: **Specific heat capacity**
  - Reasoning move: Given two substances receiving the same amount of heat energy, use specific heat capacity to predict which one's temperature will rise more, or given a desired temperature change, determine how much energy is needed.
  - Description: Specific heat capacity is the amount of energy required to raise the temperature of one gram of a substance by one degree Celsius (or one Kelvin). It quantifies a substance's resistance to temperature change. Water has an unusually high specific heat capacity (4.18 J/g-C) compared to most substances, meaning it absorbs a lot of energy before its temperature rises significantly. This is why coastal cities have milder climates than inland cities: the ocean absorbs and releases enormous amounts of heat with relatively small temperature swings. Specific heat capacity connects energy tracking (PRIM-NRG001) and heat/temperature distinction (DEF-NRG001) to quantitative prediction.
  - Semi-formal: Specific heat capacity c of substance X: q = m * c * delta-T, where q = heat energy (joules), m = mass (grams), delta-T = temperature change (degrees C). Higher c means more energy per gram per degree. For water: c = 4.18 J/(g*C). For iron: c = 0.449 J/(g*C). Same energy input raises iron's temperature approximately 9 times more than the same mass of water.
  - Depends: DEF-NRG001 (heat vs temperature -- specific heat capacity quantifies the relationship between heat added and temperature change)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Ch. 5, Section 5.2), SRC-GLB009 (Zumdahl Ch. 6, Section 6.2)
  - Referenced by: SCL
  - Tier: C
  - Real-world hook: Sand at the beach gets scorching hot by noon, but the ocean water stays cool. At night, the sand cools quickly while the water stays relatively warm. Sand has a low specific heat capacity (absorbs little energy per degree change); water has a high one. This difference drives sea breezes, moderates coastal climates, and explains why water-based heating systems are so effective.

- DEF-NRG003: **Enthalpy change (delta-H)**
  - Reasoning move: Given a chemical reaction occurring at constant pressure (typical for open-container bench chemistry), classify the reaction's enthalpy change as negative (exothermic, heat released) or positive (endothermic, heat absorbed) to predict whether the reaction heats or cools its surroundings.
  - Description: Enthalpy change (delta-H) is the net heat exchanged between a reaction system and its surroundings at constant pressure. It is the standard quantitative measure of "how much heat does this reaction produce or consume?" A negative delta-H means the reaction releases heat to the surroundings (exothermic); a positive delta-H means the reaction absorbs heat from the surroundings (endothermic). Delta-H connects the qualitative exo/endo classification (PRIM-NRG003) and the heat/temperature framework (DEF-NRG001) to a measurable, tabulated quantity. This is presented qualitatively (sign and relative magnitude, not Hess's law calculations).
  - Semi-formal: For reaction R --> P at constant pressure: delta-H = H_products - H_reactants. If delta-H < 0, reaction is exothermic (heat released = |delta-H|). If delta-H > 0, reaction is endothermic (heat absorbed = delta-H). Units: kJ/mol (energy per mole of reaction as written). Enthalpy is a state function: delta-H depends only on initial and final states, not on the path taken.
  - Depends: PRIM-NRG003 (exo/endothermic classification -- delta-H puts a quantitative sign and magnitude on the qualitative classification), DEF-NRG001 (heat vs temperature -- delta-H measures heat transfer at constant pressure)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Ch. 5, Section 5.3), SRC-GLB009 (Zumdahl Ch. 6, Section 6.3)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: The combustion of natural gas (methane) has delta-H = -890 kJ/mol -- strongly exothermic. Your gas bill is essentially paying for that negative delta-H: the energy released by burning methane heats your home. Photosynthesis has delta-H = +2803 kJ/mol per glucose -- strongly endothermic. Plants need continuous sunlight (energy input) to drive this unfavorable energy change.

- DEF-NRG004: **Free energy (conceptual)**
  - Reasoning move: Given a process where energy favorability and entropy favorability conflict, evaluate whether the combined effect (free energy) is net favorable (spontaneous) or net unfavorable (non-spontaneous) using qualitative reasoning about the relative magnitudes and the role of temperature.
  - Description: Free energy is the conceptual bookkeeping tool that combines enthalpy (energy favorability) and entropy (probability favorability) into a single measure of overall spontaneity. When delta-H and delta-S agree (both favorable or both unfavorable), the outcome is clear. When they conflict -- e.g., exothermic but entropy-decreasing, or endothermic but entropy-increasing -- free energy reasoning resolves the conflict by considering temperature as a weighting factor: at high temperature, entropy dominates; at low temperature, enthalpy dominates. This is presented conceptually, NOT as the equation delta-G = delta-H - T*delta-S. The concept is that nature balances two drives (minimize energy, maximize entropy), and temperature determines which drive wins.
  - Semi-formal: Free energy change delta-G represents combined energy-entropy favorability. Spontaneous when delta-G < 0. Qualitatively: delta-G is favorable when energy favorability (exothermic) and entropy favorability (increase) reinforce each other. When they conflict, temperature determines the winner: high T amplifies entropy's contribution; low T amplifies enthalpy's contribution.
  - Depends: PRIM-NRG005 (spontaneity reasoning -- free energy formalizes the qualitative spontaneity assessment into a single conceptual quantity)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Ch. 12, Section 12.5), SRC-GLB009 (Zumdahl Ch. 16, Section 16.5)
  - Referenced by: CHG
  - Tier: E
  - Real-world hook: Proteins fold into specific shapes spontaneously at body temperature. The folding is driven by a combination of enthalpy (favorable interactions form) and entropy (water molecules are freed from the protein surface). Neither factor alone guarantees folding -- free energy reasoning explains why it happens. At high fever temperatures, the balance shifts and proteins denature (unfold), which is why fevers above 104 F are dangerous.

- DEF-NRG005: **Calorie/joule**
  - Reasoning move: Given an energy value in calories, kilocalories (food Calories), or joules, convert between units and connect chemistry's energy measurements to everyday nutritional and energy contexts.
  - Description: The calorie (cal) is the energy needed to raise 1 gram of water by 1 degree Celsius. The food Calorie (Cal, capital C) is actually a kilocalorie (1 kcal = 1,000 cal). The joule (J) is the SI unit of energy: 1 cal = 4.184 J, so 1 food Calorie = 4,184 J = 4.184 kJ. This definition connects the abstract energy quantities in chemistry (bond energies, enthalpy changes) to the energy numbers students encounter daily on nutrition labels. It grounds NRG's abstractions in a unit system students already use, even if they do not realize they are doing energy accounting when they count Calories.
  - Semi-formal: 1 cal = 4.184 J (exact, by definition). 1 food Calorie (Cal) = 1 kcal = 1,000 cal = 4,184 J = 4.184 kJ. Energy content of foods: carbohydrates approx 4 Cal/g, proteins approx 4 Cal/g, fats approx 9 Cal/g. These are average bond energy yields from metabolic oxidation of each macronutrient.
  - Depends: DEF-NRG001 (heat vs temperature -- the calorie is defined via heat transfer to water and temperature change)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Ch. 5, Section 5.1), SRC-GLB009 (Zumdahl Ch. 6, Section 6.1)
  - Referenced by: SCL
  - Tier: C
  - Real-world hook: A nutrition label says a candy bar has 250 Calories. That means burning the candy bar's molecules (breaking C-H, C-O bonds, forming CO2 and H2O) releases 250 kcal = 1,046 kJ of energy. When you eat it, your body captures that bond energy to fuel movement, maintain body temperature, and build new molecules. Counting Calories IS energy tracking (PRIM-NRG001) applied to food.

## 5. Contested Concepts

The primary contested boundary for NRG is with CHG. Four concepts require explicit ownership resolution:

| Concept | NRG Version (Owner) | CHG Version (Owner) | Connection |
|---------|---------------------|---------------------|------------|
| Activation energy | PRIM-NRG006 (energy barrier concept -- what is the barrier, why does it exist, what lowers it) | DEF-CHG001 (catalyst -- a substance that lowers activation energy, changing rate without being consumed) | CHG imports PRIM-NRG006. NRG owns the energy concept; CHG owns the transformation concept (catalyst as a participant in the reaction mechanism). |
| Spontaneity | PRIM-NRG005 (thermodynamic favorability -- will this process occur without external driving) | CHG uses spontaneity to determine reaction direction | CHG imports PRIM-NRG005. NRG owns the favorability assessment; CHG deploys it to predict whether a reaction proceeds forward. |
| Bond energy | PRIM-NRG002 (energy stored in bonds -- net energy flow from breaking/forming bonds) | CHG uses bond energies to evaluate reaction energetics | CHG imports PRIM-NRG002. NRG owns the energy-in-bonds concept; CHG applies it within transformation contexts. |
| Equilibrium | NRG explains WHY equilibrium exists (entropy drives the system toward maximum probability) | PRIM-CHG003 (HOW equilibrium behaves -- dynamic balance, Le Chatelier's principle) | CHG owns equilibrium as a transformation concept. NRG provides the entropic driving force explanation. No NRG item is named "equilibrium" -- NRG contributes the underlying energy/entropy reasoning. |

**Governing rule (from CONVENTIONS.md Boundary Principle P2)**: NRG owns energy concepts (what energy is, how it is stored, transferred, and whether a process is favorable). CHG owns transformation concepts (what reacts, what forms, how fast, how far). When a transformation uses energy reasoning, CHG imports from NRG.

### NRG does NOT depend on STR

Bond energy reasoning (PRIM-NRG002) requires knowing that bonds exist and that breaking/forming them involves energy changes. This knowledge comes from COM-level composition analysis (PRIM-COM001: atoms exist and combine). It does NOT require knowing bond angles (PRIM-STR003), molecular polarity (DEF-STR002), or intermolecular force hierarchies (PRIM-STR004). Energy conservation, entropy, spontaneity, and activation energy are abstract principles defined without reference to molecular geometry. Two molecules with identical energy profiles can have completely different 3D structures.

## 6. Real-World Hooks

| ID | Concept | Everyday Application |
|----|---------|---------------------|
| PRIM-NRG001 | Energy tracking | Tracing energy from the granola bar you eat to the mechanical energy of your muscles and the heat your body radiates during exercise |
| PRIM-NRG002 | Bond energy reasoning | Understanding why natural gas (methane) is a good fuel: weak C-H bonds broken, strong C=O and O-H bonds formed, net energy surplus |
| PRIM-NRG003 | Exo/endothermic classification | Hand warmers (exothermic iron oxidation) vs. instant cold packs (endothermic ammonium nitrate dissolution) |
| PRIM-NRG004 | Entropy reasoning | Why ice melts at room temperature: liquid water has astronomically more molecular arrangements than ice -- melting is overwhelmingly probable |
| PRIM-NRG005 | Spontaneity reasoning | Why water freezing at -10 C and ice melting at +25 C are BOTH spontaneous -- temperature determines whether energy or entropy wins |
| PRIM-NRG006 | Activation energy reasoning | Why gasoline does not spontaneously combust in your car's fuel tank (activation barrier) but does when the spark plug fires; why a catalytic converter works |
| DEF-NRG001 | Heat vs temperature | A bathtub of lukewarm water vs. a thimble of boiling water: the bathtub holds more total thermal energy despite the lower temperature |
| DEF-NRG002 | Specific heat capacity | Why coastal San Francisco has mild weather year-round while inland Sacramento swings between extremes -- water's high specific heat moderates coastal climate |
| DEF-NRG003 | Enthalpy change (delta-H) | Your gas bill: you are paying for the negative delta-H of methane combustion (-890 kJ/mol) that heats your home |
| DEF-NRG004 | Free energy (conceptual) | Why proteins fold correctly at body temperature but denature (unfold) during high fever -- the energy-entropy balance shifts with temperature |
| DEF-NRG005 | Calorie/joule | A 250-Calorie candy bar = 1,046 kJ of chemical bond energy that your body converts to heat and motion |

## 7. Intra-Domain Dependency Graph

```
PRIM-NRG001 (Energy tracking)           PRIM-NRG004 (Entropy reasoning)
     |                                        |
     +---> PRIM-NRG002 (Bond energy)          |
     |                                        |
     +---> PRIM-NRG003 (Exo/endothermic)      |
     |          |                             |
     |          +-----------------------------+
     |          |                             |
     |          +---> PRIM-NRG005 (Spontaneity reasoning)
     |          |          |
     |          |          +---> DEF-NRG004 (Free energy, conceptual) [E]
     |          |
     |          +---> DEF-NRG003 (Enthalpy change)
     |                     |
     +---> PRIM-NRG006 (Activation energy)
     |
     +---> DEF-NRG001 (Heat vs temperature)
                |
                +---> DEF-NRG002 (Specific heat capacity)
                |
                +---> DEF-NRG003 (Enthalpy change) [also depends on PRIM-NRG003]
                |
                +---> DEF-NRG005 (Calorie/joule)
```

**Acyclicity verification**: All dependency arrows point from items with lower dependency depth to items with higher dependency depth. PRIM-NRG001 and PRIM-NRG004 are the two roots (no intra-domain dependencies). PRIM-NRG005 depends on PRIM-NRG003 and PRIM-NRG004. DEF-NRG003 depends on PRIM-NRG003 and DEF-NRG001. DEF-NRG004 depends on PRIM-NRG005. No item depends on an item of equal or greater depth through a cycle. The graph is a DAG.

**Core-only subgraph**: Removing DEF-NRG004 (E) leaves all Core items with satisfied dependencies. No Core item depends on DEF-NRG004.

## 8. Cross-Domain Interface

### Exports

| ID | Concept | Imported by |
|----|---------|-------------|
| PRIM-NRG001 | Energy tracking | CHG |
| PRIM-NRG002 | Bond energy reasoning | CHG |
| PRIM-NRG003 | Exo/endothermic classification | CHG |
| PRIM-NRG004 | Entropy reasoning | CHG |
| PRIM-NRG005 | Spontaneity reasoning | CHG |
| PRIM-NRG006 | Activation energy reasoning | CHG |
| DEF-NRG001 | Heat vs temperature | SCL |
| DEF-NRG002 | Specific heat capacity | SCL |
| DEF-NRG003 | Enthalpy change (delta-H) | CHG |
| DEF-NRG004 | Free energy (conceptual) | CHG |
| DEF-NRG005 | Calorie/joule | SCL |

### Imports

| DEP ID | Imported Item | From Domain | Used by |
|--------|---------------|-------------|---------|
| DEP-NRG001 | PRIM-COM001 (Atomic composition analysis) | COM | PRIM-NRG001 (energy tracking requires knowing what atoms/bonds are present) |
| DEP-NRG002 | PRIM-COM006 (Conservation of atoms) | COM | Conceptual scaffold: energy conservation parallels atom conservation |

## 9. Difficulty Tiers

| ID | Concept | Tier | Justification |
|----|---------|------|---------------|
| PRIM-NRG001 | Energy tracking | C | Foundational: every subsequent NRG concept requires the ability to trace energy through a system |
| PRIM-NRG002 | Bond energy reasoning | C | Core predictive tool: connects molecular bonds to observable energy flow; corrects the pervasive "bond breaking releases energy" misconception |
| PRIM-NRG003 | Exo/endothermic classification | C | Core binary classification: the first question asked about any energy-involving process is "exo or endo?" |
| PRIM-NRG004 | Entropy reasoning | C | Core probabilistic reasoning: without entropy, students believe only exothermic processes are spontaneous -- a fundamental misconception |
| PRIM-NRG005 | Spontaneity reasoning | C | Core synthesis: combines the two pillars (energy + entropy) into the central question of the domain -- will this process occur? |
| PRIM-NRG006 | Activation energy reasoning | C | Core explanatory tool: resolves the paradox of favorable but non-occurring processes; essential for understanding catalysts (CHG) |
| DEF-NRG001 | Heat vs temperature | C | Core distinction: the most commonly conflated concepts in introductory chemistry; required for specific heat, enthalpy, and calorie definitions |
| DEF-NRG002 | Specific heat capacity | C | Core quantitative bridge: explains real-world phenomena (climate moderation, cooking) and is required for SCL's deployment of energy calculations |
| DEF-NRG003 | Enthalpy change (delta-H) | C | Core measurable quantity: connects qualitative exo/endo classification to tabulated, comparable values; essential for CHG's reaction energetics |
| DEF-NRG004 | Free energy (conceptual) | E | Enrichment: valuable conceptual synthesis but not required by any Core item; omitting it does not break any dependency chain; PRIM-NRG005 already provides Core-level spontaneity reasoning |
| DEF-NRG005 | Calorie/joule | C | Core literacy bridge: connects chemistry's energy units to everyday nutritional contexts; essential for non-majors who encounter Calories daily |

**Tier constraint verification**: The sole Enrichment item is DEF-NRG004 (Free energy, conceptual). No Core item depends on DEF-NRG004; it depends only on PRIM-NRG005 (C). Removing DEF-NRG004 leaves all 10 Core items with fully satisfied dependency chains. The Core tier alone forms a self-contained, dependency-complete sub-taxonomy.

## 10. Self-Audit Checklist

- [x] Every PRIM has: reasoning move formulation ("Given X, do Y to determine Z"), description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [x] Every DEF depends only on previously listed PRIM/DEF (check intra-domain dependency graph: DEF-NRG001 depends on PRIM-NRG001; DEF-NRG002 depends on DEF-NRG001; DEF-NRG003 depends on PRIM-NRG003 and DEF-NRG001; DEF-NRG004 depends on PRIM-NRG005; DEF-NRG005 depends on DEF-NRG001)
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format (PRIM-COM001, PRIM-COM006, DEF-CHG001, PRIM-CHG003, etc.)
- [x] Every import is listed in the source domain's exports (PRIM-COM001 and PRIM-COM006 are both listed in COM's exports in DOMAIN-COM.md Section 8; NRG's exports match the Primitive Registry in CONVENTIONS.md Section 9)
- [x] Dissolution argument is present and non-trivial (4 sentences explaining why NRG cannot merge into STR, CHG, or any other domain; includes concrete examples of identical energy profiles with different structures)
- [x] Real-world hooks cover everyday non-major contexts (cooking, climate, batteries/cars, hand warmers, cold packs, nutrition, exercise, gas bills, beach sand, protein folding/fever)
- [x] Intra-domain dependency graph is acyclic (verified: two roots PRIM-NRG001 and PRIM-NRG004; all edges point from lower depth to higher depth; no cycles)
- [x] Tier annotations (C/E) are present on all 11 items (10 Core + 1 Enrichment)
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry in CONVENTIONS.md Section 9: no NRG concept appears in COM, STR, CHG, or SCL)
- [x] Reasoning moves are genuinely "Given X, do Y" cognitive operations (not mere topic labels or vocabulary words: each PRIM specifies input, operation, and output; each DEF specifies a distinction or conversion grounded in prior PRIMs)
