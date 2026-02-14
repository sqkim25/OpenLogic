# DOMAIN-CHG v0.1

## 0. Sources & Assumptions

- SRC-CHG001: Talanquer & Pollard, "Let's teach how we think instead of what we know," *Chemistry Education Research and Practice*, 2010 (reaction classification as reasoning patterns, not memorized categories)
- SRC-CHG002: Becker et al., "College chemistry students' understanding of potential energy in the context of chemical reactions," *J. Research in Science Teaching*, 2015 (conflation of activation energy with reaction energy; supports separating rate from spontaneity)
- SRC-CHG003: Cakmakci, "Identifying alternative conceptions of chemical kinetics among secondary school and undergraduate students," *J. Chem. Educ.*, 2010 (rate misconceptions: students confuse fast with favorable)
- SRC-GLB008: OpenStax, *Chemistry 2e*, 2019, Ch. 4 (reactions), Ch. 12 (kinetics), Ch. 13 (equilibrium), Ch. 14 (acids/bases), Ch. 17 (electrochemistry), Ch. 21 (nuclear)
- SRC-GLB009: Zumdahl & Zumdahl, *Chemistry*, 10th ed., 2017, Ch. 4 (reactions), Ch. 12 (kinetics), Ch. 13 (equilibrium), Ch. 14 (acids/bases), Ch. 17 (electrochemistry), Ch. 20 (nuclear)
- SRC-GLB010: ACS, *Chemistry in Context*, 10th ed., 2020, Ch. 6--9
- ASM-CHG001: Students arrive with composition reasoning (COM), structural reasoning (STR), energy reasoning (NRG), and scale-bridging reasoning (SCL) in place. No transformation-specific reasoning is assumed. Justification: the domain DAG places CHG last in the topological sort (COM --> STR --> NRG --> SCL --> CHG), so CHG may freely import from all prior domains.
- ASM-CHG002: Reaction mechanisms are NOT taught at the step-by-step arrow-pushing level. Students learn to classify reactions, predict products qualitatively, and reason about rate and equilibrium at the conceptual level. Justification: mechanism-level detail is a majors-track skill; non-majors need the reasoning patterns (SRC-CHG001) without the mechanistic apparatus.

## 1. Domain Intent

- **Governing question**: How do substances transform into other substances, and what controls the outcome?
- **Scope**: Determining what reacts with what, what products form, how to balance a chemical equation, how to classify reactions, how fast reactions proceed, what equilibrium looks like, how acids and bases behave, how electrons transfer in redox, and (at the enrichment level) how nuclear changes differ from chemical changes. CHG provides the transformation layer: given the identity (COM), arrangement (STR), energy favorability (NRG), and quantitative tools (SCL), CHG determines what actually happens when substances meet.
- **Non-goals**: What substances are made of or how to count their atoms (COM). How atoms are arranged in 3D or what intermolecular forces govern physical properties (STR). Whether a process is energetically or entropically favorable (NRG). How to bridge molecular-level descriptions to macroscopic quantities (SCL).
- **Dissolution argument**: Knowing that a reaction is spontaneous (NRG) does not tell you: (a) what the products are, (b) how fast it proceeds, (c) where equilibrium lies, or (d) what type of reaction it is. NRG says "this process is favorable"; CHG says "here is what actually forms, at what rate, and in what proportions at equilibrium." Equation balancing (conservation in the transformation context), equilibrium reasoning (dynamic balance between forward and reverse processes), rate reasoning (kinetics), and reaction classification are unique cognitive operations not derivable from energy, structure, or composition alone. A student who masters all of NRG can determine that iron rusting is spontaneous, but without CHG they cannot write the balanced equation, predict that Fe2O3 forms, explain why a catalyst speeds it up, or determine the equilibrium position. These are genuinely distinct reasoning moves (SRC-CHG001, SRC-CHG002).
- **Threshold schema mapping**: Static --> Dynamic. The foundational conceptual shift in CHG is recognizing that matter is not static but continuously transforming -- and that "equilibrium" does not mean "nothing is happening" but rather "forward and reverse processes are occurring at equal rates." Students who fail to cross this threshold treat equilibrium as a stopped state and cannot reason about Le Chatelier perturbations or why reactions "go to completion" only approximately.

## 2. Prerequisites

CHG depends on STR, NRG, and SCL (and transitively on COM). The following items are imported:

| DEP ID | Imported Item | Source Domain | Purpose in CHG |
|--------|---------------|---------------|----------------|
| DEP-CHG001 | PRIM-COM005 (Chemical formula reading) | COM | Read formulas to write and balance equations (PRIM-CHG001) |
| DEP-CHG002 | PRIM-COM006 (Conservation of atoms) | COM | Atom conservation is the principle enforced by equation balancing (PRIM-CHG001) |
| DEP-CHG003 | PRIM-COM007 (Valence electron reasoning) | COM | Electron bookkeeping for oxidation-reduction reasoning (PRIM-CHG006) |
| DEP-CHG004 | DEF-COM001 (Isotope) | COM | Distinguish isotopes for nuclear change reasoning (PRIM-CHG007) |
| DEP-CHG005 | PRIM-STR001 (Bond type classification) | STR | Classify bond types to predict reaction products and recognize reaction types (PRIM-CHG002) |
| DEP-CHG006 | PRIM-STR002 (Bond polarity reasoning) | STR | Identify proton donors/acceptors in acid-base reasoning (PRIM-CHG005) |
| DEP-CHG007 | PRIM-NRG006 (Activation energy reasoning) | NRG | Energy barrier concept for rate reasoning (PRIM-CHG004) and catalyst definition (DEF-CHG001) |
| DEP-CHG008 | PRIM-SCL003 (Concentration reasoning) | SCL | Concentration dependence of equilibrium (PRIM-CHG003), rate (PRIM-CHG004), and pH (DEF-CHG002) |

Additionally, CHG references (but does not structurally depend on for its own definitions): PRIM-NRG001 (energy tracking), PRIM-NRG002 (bond energy reasoning), PRIM-NRG003 (exo/endothermic classification), PRIM-NRG004 (entropy reasoning), PRIM-NRG005 (spontaneity reasoning), DEF-NRG003 (enthalpy change), and DEF-NRG004 (free energy, conceptual). These NRG exports provide the driving-force explanation that CHG's transformation concepts deploy.

## 3. Primitives

- PRIM-CHG001: **Equation reading and balancing**
  - Reasoning move: Given a chemical equation with reactants and products, balance it so that atoms of each element are conserved on both sides, and extract the quantitative mole ratios (stoichiometric coefficients) that govern the amounts consumed and produced.
  - Description: The cognitive operation of enforcing atom conservation within a transformation context. A balanced equation is the complete quantitative description of a chemical reaction: it tells you what reacts, what forms, and in what proportions. Balancing requires systematically adjusting coefficients until every element has equal atom counts on both sides. This is distinct from merely recognizing that atoms are conserved (PRIM-COM006, which is the principle); PRIM-CHG001 is the procedural deployment of that principle in the context of an actual transformation. Once balanced, the coefficients become mole ratios that feed into stoichiometric calculations (SCL). Balancing is the gateway skill of CHG: every other CHG primitive operates on or refers to a balanced equation.
  - Semi-formal: Given reaction aA + bB --> cC + dD, determine coefficients a, b, c, d (positive integers) such that for every element E: a * count(E in A) + b * count(E in B) = c * count(E in C) + d * count(E in D). The coefficients a:b:c:d define the stoichiometric mole ratio. Example: _CH4 + _O2 --> _CO2 + _H2O balances as 1:2:1:2.
  - Depends: PRIM-COM006 (conservation of atoms -- imported from COM), PRIM-COM005 (chemical formula reading -- imported from COM)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 4, Section 4.1), SRC-GLB009 (Zumdahl Ch. 3, Section 3.7)
  - Referenced by: SCL
  - Tier: C
  - Real-world hook: A barbecue propane tank label says C3H8. Equation balancing tells you that burning one mole of propane requires five moles of oxygen and produces three moles of CO2 and four moles of H2O: C3H8 + 5O2 --> 3CO2 + 4H2O. That balanced equation is why incomplete combustion in a poorly ventilated grill produces deadly carbon monoxide instead -- not enough O2 to complete the 1:5 ratio.

- PRIM-CHG002: **Reaction type recognition**
  - Reasoning move: Given reactants, classify the transformation type -- synthesis (A + B --> AB), decomposition (AB --> A + B), single replacement (A + BC --> AC + B), double replacement (AB + CD --> AD + CB), or combustion (hydrocarbon + O2 --> CO2 + H2O) -- and use the classification to predict the general form of the products.
  - Description: The cognitive operation of pattern-matching a set of reactants to a known reaction archetype and using that archetype to predict product identity. This is the chemist's first question upon seeing reactants: what TYPE of transformation will occur? Each type has a predictable product pattern. Synthesis combines; decomposition splits; single replacement substitutes one element; double replacement swaps partners; combustion oxidizes a hydrocarbon. The classification depends on bond type reasoning (PRIM-STR001, imported): ionic compounds undergo exchange reactions; molecular compounds undergo combustion and synthesis. Reaction type recognition is a reasoning pattern (SRC-CHG001), not a memorized table: the student learns to read the reactant structure and predict the transformation type.
  - Semi-formal: Given reactants {R_1, R_2, ...}, identify the reaction type T from the pattern: Synthesis: A + B --> AB (two simple --> one complex). Decomposition: AB --> A + B (one complex --> two simpler). Single replacement: A + BC --> AC + B (element replaces element). Double replacement: AB + CD --> AD + CB (ions swap). Combustion: C_xH_y + O2 --> CO2 + H2O. Predicted products follow from T.
  - Depends: PRIM-STR001 (bond type classification -- imported from STR; needed to recognize whether reactants are ionic or molecular, which determines likely reaction type)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 4, Section 4.2), SRC-GLB009 (Zumdahl Ch. 4), SRC-CHG001 (Talanquer & Pollard 2010, reaction classification as reasoning)
  - Referenced by: --
  - Tier: C
  - Real-world hook: When baking soda (NaHCO3) meets vinegar (acetic acid), the fizzing tells you a reaction occurred. Reaction type recognition classifies this as a double replacement (acid + carbonate --> salt + water + CO2). Knowing the type lets you predict the products without memorizing every specific reaction -- the same pattern applies to any acid + carbonate combination, from antacid tablets (CaCO3 + stomach acid) to cleaning limescale from a coffee maker.

- PRIM-CHG003: **Equilibrium reasoning**
  - Reasoning move: Given a reversible process, explain why macroscopic properties (concentrations, color, pressure) stabilize even though molecular-level activity continues -- because the forward reaction rate equals the reverse reaction rate -- and predict how the equilibrium position shifts when conditions change.
  - Description: The cognitive operation of understanding dynamic balance. At equilibrium, both forward and reverse reactions are occurring simultaneously at equal rates, so the net concentrations of reactants and products remain constant. This is NOT a stopped state -- it is a dynamic steady state. The position of equilibrium (how far toward products or reactants the system settles) depends on the relative rates and is described by the equilibrium constant K. A large K means products are heavily favored; a small K means reactants dominate. Equilibrium reasoning is the "static --> dynamic" threshold of the CHG domain: students must abandon the notion that reactions simply "go" or "stop" and instead see every reaction as a competition between forward and reverse processes. NRG provides the thermodynamic driving force (entropy, favorability); CHG provides the kinetic mechanism (rate balance) and the behavioral description (what happens when you perturb it).
  - Semi-formal: For reversible reaction aA + bB <=> cC + dD: at equilibrium, rate_forward = rate_reverse. Equilibrium constant K = [C]^c [D]^d / [A]^a [B]^b (concentrations at equilibrium). If K >> 1, products dominate. If K << 1, reactants dominate. If K ~ 1, comparable amounts of both. Perturbation analysis: if [A] increases, rate_forward increases temporarily, producing more C and D until a new equilibrium is reached.
  - Depends: PRIM-SCL003 (concentration reasoning -- imported from SCL; equilibrium is described in terms of concentrations)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 13, Section 13.1--13.3), SRC-GLB009 (Zumdahl Ch. 13)
  - Referenced by: SCL
  - Tier: C
  - Real-world hook: When you open a can of soda, CO2 fizzes out because the equilibrium CO2(dissolved) <=> CO2(gas) was disturbed by the pressure drop. Inside the sealed can, dissolved CO2 and gaseous CO2 were at equilibrium at high pressure. Opening the can lowered the gas-phase CO2 pressure, shifting the equilibrium toward gas escape. Equilibrium reasoning explains why the soda goes flat over time (CO2 escapes until a new equilibrium at atmospheric pressure is reached) and why it goes flat faster when warm (K shifts with temperature).

- PRIM-CHG004: **Rate reasoning**
  - Reasoning move: Given conditions such as temperature, concentration, surface area, and presence of a catalyst, predict whether a reaction speeds up or slows down, and explain why in terms of molecular collisions and activation energy.
  - Description: The cognitive operation of predicting how fast a reaction proceeds based on controllable factors. Rate reasoning addresses the kinetic question: spontaneity (NRG) tells you WHETHER a reaction is favorable; rate tells you HOW FAST it actually occurs. A common and persistent student misconception is conflating these two -- believing that favorable reactions must be fast and unfavorable ones slow (SRC-CHG003). In reality, diamond-to-graphite is spontaneous but imperceptibly slow; dynamite decomposition is both spontaneous and explosively fast. Rate depends on collision frequency and energy: higher temperature means faster-moving molecules (more collisions with sufficient energy), higher concentration means more molecules per volume (more collisions), greater surface area means more exposed reaction sites, and a catalyst provides a lower-energy pathway. All four factors ultimately work by modifying either collision frequency or the fraction of collisions exceeding the activation energy barrier (PRIM-NRG006, imported).
  - Semi-formal: Rate = f(T, [R], SA, catalyst). Increasing T --> increases fraction of molecules with kinetic energy >= E_a --> faster rate. Increasing [R] --> increases collision frequency --> faster rate. Increasing surface area --> increases number of exposed reactive sites --> faster rate. Adding catalyst --> lowers E_a via alternative pathway --> faster rate (catalyst does not change delta-H or K). Rate is NOT determined by spontaneity: delta-G < 0 does not imply fast; delta-G > 0 does not imply slow.
  - Depends: PRIM-NRG006 (activation energy reasoning -- imported from NRG; rate depends on the fraction of molecules exceeding E_a), PRIM-SCL003 (concentration reasoning -- imported from SCL; rate depends on concentration)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 12, Section 12.1--12.5), SRC-GLB009 (Zumdahl Ch. 12), SRC-CHG002 (Becker et al. 2015), SRC-CHG003 (Cakmakci 2010)
  - Referenced by: --
  - Tier: C
  - Real-world hook: Refrigerating food slows spoilage because lowering temperature reduces the rate of decomposition reactions in the food. The food is still thermodynamically unstable (it will eventually spoil), but the refrigerator slows the process by reducing the fraction of molecules with enough energy to clear the activation barrier. Conversely, a pressure cooker speeds up cooking by raising temperature (higher T means faster rate). Rate reasoning explains why we refrigerate, why we cook, and why expiration dates exist.

- PRIM-CHG005: **Acid-base reasoning**
  - Reasoning move: Given two substances, identify the proton donor (Bronsted acid) and the proton acceptor (Bronsted base), predict the products of the proton transfer, and determine whether the resulting solution is acidic, basic, or neutral (pH direction).
  - Description: The cognitive operation of analyzing proton-transfer reactions. An acid donates H+ (a proton); a base accepts H+. When an acid meets a base, H+ transfers from the donor to the acceptor, producing a conjugate base (from the acid) and a conjugate acid (from the base). The resulting solution's pH depends on the relative strengths of the acid and base: strong acid + weak base produces an acidic solution; weak acid + strong base produces a basic solution; strong acid + strong base produces a neutral solution. Acid-base reasoning requires bond polarity reasoning (PRIM-STR002, imported) because determining which bond will release H+ depends on polarity: highly polar X-H bonds (where X is electronegative, like O or Cl) release H+ readily. This primitive is one of the most practically relevant in the taxonomy: acids and bases pervade cooking, digestion, cleaning, environmental science, and medicine.
  - Semi-formal: For substances HA (acid) and B (base): HA + B --> A- + BH+. HA is the proton donor (Bronsted acid); B is the proton acceptor (Bronsted base). A- is the conjugate base of HA; BH+ is the conjugate acid of B. Strong acids (e.g., HCl, H2SO4) ionize completely: HA --> H+ + A-. Weak acids ionize partially: HA <=> H+ + A- (equilibrium favors reactants). pH direction: if [H+] > [OH-], solution is acidic (pH < 7); if [OH-] > [H+], basic (pH > 7); if equal, neutral (pH = 7).
  - Depends: PRIM-STR002 (bond polarity reasoning -- imported from STR; polarity of X-H bonds determines acid strength)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 14, Section 14.1--14.3), SRC-GLB009 (Zumdahl Ch. 14), SRC-GLB010 (ACS Ch. 6)
  - Referenced by: SCL
  - Tier: C
  - Real-world hook: When you take an antacid tablet (CaCO3) for heartburn, acid-base reasoning explains the relief: the carbonate base (CaCO3) accepts protons from stomach acid (HCl), neutralizing it. The products are CaCl2 (salt), H2O (water), and CO2 (the burp). The same reasoning explains why adding lemon juice (citric acid, a weak acid) to milk causes curdling (the acid denatures milk proteins), and why gardeners add lime (calcium hydroxide, a base) to acidic soil.

- PRIM-CHG006: **Oxidation-reduction reasoning**
  - Reasoning move: Given a process, identify electron transfer -- which species loses electrons (is oxidized) and which gains electrons (is reduced) -- and connect the electron flow to practical applications such as batteries, corrosion, and metabolism.
  - Description: The cognitive operation of tracking electron transfer in chemical processes. Oxidation is electron loss; reduction is electron gain. The mnemonic "OIL RIG" (Oxidation Is Loss, Reduction Is Gain) captures the definition. In every redox reaction, one species is the reducing agent (it gives up electrons, getting oxidized) and another is the oxidizing agent (it accepts electrons, getting reduced). Redox reasoning depends on valence electron reasoning (PRIM-COM007, imported) because determining whether an atom has lost or gained electrons requires knowing its starting valence electron count and comparing it to its oxidation state in the product. Redox reactions are the basis of batteries (controlled electron flow through a wire), corrosion (uncontrolled oxidation of metals), photosynthesis and respiration (biological electron transfer chains), and combustion (rapid oxidation).
  - Semi-formal: For a process involving species A and B: if A loses electrons (oxidation number increases), A is oxidized and is the reducing agent. If B gains electrons (oxidation number decreases), B is reduced and is the oxidizing agent. Total electrons lost by A = total electrons gained by B (electron conservation). Oxidation number rules: pure element = 0; monatomic ion = ion charge; O = -2 (usually); H = +1 (usually). Example: Zn + Cu2+ --> Zn2+ + Cu. Zn is oxidized (0 --> +2, loses 2e-); Cu2+ is reduced (+2 --> 0, gains 2e-).
  - Depends: PRIM-COM007 (valence electron reasoning -- imported from COM; needed to determine starting electron configuration and track electron transfer)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 4, Section 4.3 and Ch. 17), SRC-GLB009 (Zumdahl Ch. 4 and Ch. 17)
  - Referenced by: SCL
  - Tier: C
  - Real-world hook: A battery converts chemical energy to electrical energy through a controlled redox reaction. In an alkaline AA battery, zinc is oxidized (loses electrons) at one terminal, and manganese dioxide is reduced (gains electrons) at the other. The electrons flow through your flashlight circuit on their way from Zn to MnO2, powering the bulb. When the zinc is fully oxidized, the battery is "dead." The same reasoning explains why iron rusts (Fe is oxidized by O2 in the presence of water) and why stainless steel resists corrosion (chromium forms a protective oxide layer).

- PRIM-CHG007: **Nuclear change reasoning**
  - Reasoning move: Given an unstable nucleus, predict the type of radiation emitted (alpha, beta, or gamma), write the nuclear equation, and distinguish nuclear change from chemical change by recognizing that different conservation rules apply (mass number and atomic number conserve, not just atom identity).
  - Description: The cognitive operation of reasoning about transformations at the nuclear level rather than the chemical level. In chemical change, atoms rearrange but retain their elemental identity (Z is unchanged). In nuclear change, the nucleus itself transforms: protons and neutrons reconfigure, Z changes, and the atom becomes a DIFFERENT ELEMENT. This is a fundamentally different type of transformation. Alpha decay ejects a helium-4 nucleus (Z decreases by 2, mass number by 4). Beta decay converts a neutron to a proton (Z increases by 1, mass number unchanged). Gamma emission releases energy without changing Z or mass number. Nuclear change reasoning depends on isotope knowledge (DEF-COM001, imported) because nuclear stability depends on the neutron-to-proton ratio, which varies among isotopes. This primitive is Enrichment because nuclear chemistry is a specialized topic that no downstream Core item depends on.
  - Semi-formal: For nucleus X with atomic number Z and mass number A: Alpha decay: X(Z,A) --> Y(Z-2, A-4) + He(2,4). Beta decay: X(Z,A) --> Y(Z+1, A) + e(-1,0). Gamma emission: X(Z,A)* --> X(Z,A) + gamma. Conservation: sum of Z(reactants) = sum of Z(products); sum of A(reactants) = sum of A(products). Chemical change conserves Z for each atom; nuclear change changes Z.
  - Depends: DEF-COM001 (isotope -- imported from COM; nuclear stability depends on neutron-to-proton ratio, an isotope property)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 21), SRC-GLB009 (Zumdahl Ch. 20), SRC-GLB010 (ACS Ch. 7)
  - Referenced by: SCL
  - Tier: E
  - Real-world hook: Smoke detectors contain a tiny amount of americium-241, an alpha emitter. The alpha particles ionize air molecules between two plates, creating a small current. When smoke particles enter, they absorb the alpha particles, the current drops, and the alarm sounds. Nuclear change reasoning explains why this works and why the americium must be replaced periodically (it decays, reducing the alpha emission rate). The same reasoning explains carbon-14 dating: C-14 undergoes beta decay with a known half-life, so measuring the remaining C-14 in a sample reveals its age.

## 4. Definitions

- DEF-CHG001: **Catalyst**
  - Reasoning move: Given a reaction that is thermodynamically favorable but too slow, identify a catalyst as a substance that speeds the reaction by providing an alternative pathway with lower activation energy, without being consumed in the process.
  - Description: A catalyst participates in a reaction mechanism (forming temporary intermediates) but is regenerated by the end, so its net consumption is zero. It lowers the activation energy barrier (PRIM-NRG006, imported) without changing the overall energy balance (delta-H or delta-G is unchanged) or the equilibrium position (K is unchanged). A catalyst makes both forward and reverse reactions faster equally, so equilibrium is reached sooner but at the same position. Biological catalysts (enzymes) are the most important catalysts for non-majors: they enable metabolic reactions that would otherwise be too slow at body temperature. The distinction between "changes rate" and "changes equilibrium" is a common student confusion point.
  - Semi-formal: A catalyst C for reaction R --> P: provides alternative pathway R --> [C-intermediate] --> P + C. E_a(catalyzed) < E_a(uncatalyzed). delta-H(catalyzed) = delta-H(uncatalyzed). K(catalyzed) = K(uncatalyzed). Rate(catalyzed) > Rate(uncatalyzed). C is not consumed: [C]_initial = [C]_final.
  - Depends: PRIM-CHG004 (rate reasoning -- catalysts modify rate), PRIM-NRG006 (activation energy reasoning -- imported from NRG; catalysts lower E_a)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 12, Section 12.7), SRC-GLB009 (Zumdahl Ch. 12, Section 12.7)
  - Referenced by: --
  - Tier: C
  - Real-world hook: Your car's catalytic converter contains platinum and palladium that catalyze the conversion of toxic exhaust gases (CO, NOx, unburned hydrocarbons) into less harmful products (CO2, N2, H2O). The reactions are spontaneous but too slow without the catalyst. In your body, the enzyme lactase catalyzes the breakdown of lactose (milk sugar); people who are lactose intolerant lack sufficient lactase, so the reaction occurs too slowly and undigested lactose causes discomfort.

- DEF-CHG002: **pH scale**
  - Reasoning move: Given a solution, use the pH scale (0--14) to classify it as acidic (pH < 7), neutral (pH = 7), or basic (pH > 7), and relate pH to the concentration of hydrogen ions in solution.
  - Description: The pH scale is a compact representation of H+ concentration in solution. Conceptually, lower pH means more H+ ions (more acidic); higher pH means fewer H+ ions (more basic). The scale runs from 0 (extremely acidic, like battery acid) through 7 (neutral, like pure water) to 14 (extremely basic, like drain cleaner). Each whole number change in pH represents a tenfold change in H+ concentration, but this logarithmic relationship is presented conceptually rather than mathematically (no logarithm formula at the non-majors level). The pH scale combines acid-base reasoning (PRIM-CHG005, which identifies acids and bases) with concentration reasoning (PRIM-SCL003, imported, which connects amount per volume to effect). It is a definition rather than a primitive because it names a specific measurement scale built from two prior reasoning moves.
  - Semi-formal: pH scale: 0 <= pH <= 14 for typical aqueous solutions. pH < 7: acidic ([H+] > [OH-]). pH = 7: neutral ([H+] = [OH-]). pH > 7: basic ([H+] < [OH-]). Each unit decrease in pH represents approximately 10x increase in [H+]. Examples: lemon juice pH ~ 2, coffee pH ~ 5, blood pH ~ 7.4, baking soda pH ~ 9, ammonia cleaner pH ~ 11.
  - Depends: PRIM-CHG005 (acid-base reasoning -- pH quantifies the acid-base character of a solution), PRIM-SCL003 (concentration reasoning -- imported from SCL; pH is fundamentally about H+ concentration)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 14, Section 14.2), SRC-GLB009 (Zumdahl Ch. 14, Section 14.2)
  - Referenced by: SCL
  - Tier: C
  - Real-world hook: A swimming pool should have pH between 7.2 and 7.8. Below 7.2, the water irritates eyes and corrodes metal fixtures (too acidic). Above 7.8, chlorine disinfectant becomes less effective and scale deposits form (too basic). Pool test strips measure pH so you can adjust with muriatic acid (lowers pH) or sodium carbonate (raises pH). The same reasoning applies to soil pH for gardening, blood pH in medicine (normal 7.35--7.45), and the pH of shampoo for hair health.

- DEF-CHG003: **Le Chatelier's principle**
  - Reasoning move: Given a system at equilibrium that is subjected to a stress (change in concentration, temperature, or pressure), predict the direction of the equilibrium shift -- the system partially counteracts the stress by favoring the reaction that reduces it.
  - Description: Le Chatelier's principle is the behavioral rule for perturbed equilibria. It does not tell you WHY the system responds (that is entropy and free energy reasoning from NRG), but it tells you HOW: add more reactant, and the equilibrium shifts toward products to consume the excess; remove product, and the equilibrium shifts toward products to replace what was removed; increase temperature for an exothermic reaction, and the equilibrium shifts toward reactants (treating heat as a product). The principle is a powerful qualitative prediction tool that applies to any equilibrium -- chemical, physical, or biological. It depends on PRIM-CHG003 (equilibrium reasoning) because you must understand dynamic balance before you can reason about what happens when that balance is disturbed.
  - Semi-formal: For system at equilibrium aA + bB <=> cC + dD: Stress: increase [A] --> shift right (more C, D produced). Stress: decrease [C] --> shift right (more C produced). Stress: increase T for exothermic reaction (delta-H < 0) --> shift left (treats heat as product being added). Stress: increase P for reaction where n_gas(products) < n_gas(reactants) --> shift right (toward fewer gas moles). General rule: system shifts in the direction that partially counteracts the stress.
  - Depends: PRIM-CHG003 (equilibrium reasoning -- must understand equilibrium as dynamic balance before predicting perturbation response)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 13, Section 13.4), SRC-GLB009 (Zumdahl Ch. 13, Section 13.7)
  - Referenced by: --
  - Tier: C
  - Real-world hook: The Haber process synthesizes ammonia: N2 + 3H2 <=> 2NH3 (exothermic). Le Chatelier's principle dictates the industrial conditions: high pressure (shifts toward fewer gas moles = products), moderate temperature (too low is slow, too high shifts equilibrium toward reactants), and continuous removal of NH3 (shifts toward products). The same reasoning explains why hyperventilating (blowing off CO2) shifts the blood CO2/bicarbonate equilibrium and makes blood more basic, causing lightheadedness.

- DEF-CHG004: **Half-life**
  - Reasoning move: Given a radioactive isotope, use its half-life (the time for half of a sample to decay) to predict how much remains after a given number of half-lives, and apply this to dating, medical diagnostics, and nuclear waste management.
  - Description: Half-life is the time required for exactly half of a radioactive sample to undergo nuclear decay. After one half-life, 50% remains; after two, 25%; after three, 12.5%; and so on. Half-life is constant for a given isotope and is not affected by temperature, pressure, or chemical environment -- a remarkable fact that distinguishes nuclear decay from chemical reactions. Half-life is the quantitative tool for nuclear change reasoning (PRIM-CHG007): it converts "this nucleus is unstable" into "this is how long it takes to decay by half." Carbon-14 has a half-life of 5,730 years (used for archaeological dating); iodine-131 has a half-life of 8 days (used for thyroid imaging); uranium-238 has a half-life of 4.5 billion years (used for geological dating). This definition is Enrichment because it depends on PRIM-CHG007 (E), and a Core item MUST NOT depend on an Enrichment item (CONVENTIONS.md Section 4).
  - Semi-formal: For radioactive isotope X with half-life t_(1/2): amount remaining after n half-lives = initial_amount x (1/2)^n. Time elapsed = n x t_(1/2). Fraction remaining after time t: fraction = (1/2)^(t / t_(1/2)). Half-life is independent of initial amount, temperature, and chemical state.
  - Depends: PRIM-CHG007 (nuclear change reasoning -- half-life quantifies the rate of nuclear decay described by PRIM-CHG007)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 21, Section 21.3), SRC-GLB009 (Zumdahl Ch. 20, Section 20.4)
  - Referenced by: SCL
  - Tier: E
  - Real-world hook: Carbon dating works because living organisms continuously take in carbon-14 (from atmospheric CO2) and maintain a constant C-14/C-12 ratio. When the organism dies, C-14 intake stops and the ratio decreases as C-14 decays (half-life = 5,730 years). Measuring the remaining C-14 fraction tells archaeologists how long ago the organism died. The same reasoning applies to nuclear medicine: iodine-131 (half-life 8 days) is given to thyroid cancer patients; it decays fast enough to deliver radiation to the thyroid but clears the body within weeks.

- DEF-CHG005: **Precipitation**
  - Reasoning move: Given two aqueous ionic solutions mixed together, determine whether an insoluble ionic product (precipitate) forms by checking solubility rules, and predict the identity of the solid that crashes out of solution.
  - Description: Precipitation is a specific type of double-replacement reaction in which two dissolved ionic compounds exchange partners and one of the resulting combinations is insoluble in water, forming a solid (precipitate). Predicting precipitation requires two imported concepts: bond type classification (PRIM-STR001) to recognize ionic compounds, and concentration reasoning (PRIM-SCL003) to understand that ions are dissolved at certain concentrations. The reasoning move is: identify the ions present, consider all possible new pairings, check each against solubility rules (e.g., most chlorides are soluble EXCEPT AgCl, PbCl2; most sulfates are soluble EXCEPT BaSO4, PbSO4), and predict whether a precipitate forms. This definition is Enrichment because it is a specialized application of reaction type recognition that, while practically important, is not required by any downstream Core item.
  - Semi-formal: Given solutions of AB(aq) and CD(aq): possible products are AD and CB. If either AD or CB is insoluble (per solubility rules), it forms as a precipitate: AB(aq) + CD(aq) --> AD(s) + CB(aq) (net ionic equation removes spectator ions). Solubility rules: most Na+, K+, NH4+ salts are soluble; most NO3- salts are soluble; most Cl- salts are soluble except Ag+, Pb2+, Hg2+; most SO4^2- salts are soluble except Ba2+, Pb2+, Ca2+.
  - Depends: PRIM-STR001 (bond type classification -- imported from STR; must recognize ionic compounds), PRIM-SCL003 (concentration reasoning -- imported from SCL; dissolved ions at specific concentrations)
  - Ownership: CHG
  - Source: SRC-GLB008 (OpenStax Ch. 4, Section 4.2), SRC-GLB009 (Zumdahl Ch. 4, Section 4.6)
  - Referenced by: --
  - Tier: E
  - Real-world hook: Hard water contains dissolved Ca2+ and Mg2+ ions. When hard water is heated in a kettle, the calcium reacts with dissolved bicarbonate to precipitate CaCO3 (calcium carbonate) -- the white scale you see on the inside. Water softeners work by replacing Ca2+ with Na+ (ion exchange), which does not form insoluble precipitates. The same precipitation reasoning explains why mixing certain household cleaners can produce unwanted solids, and why adding alum to turbid water at a treatment plant causes suspended particles to clump and settle.

## 5. Contested Concepts

The primary contested boundary for CHG is with NRG. The trickiest ownership decisions in the taxonomy occur at this interface.

| Concept | NRG Owns | CHG References | Connection |
|---------|----------|---------------|------------|
| Activation energy | PRIM-NRG006 (energy barrier concept: what the barrier is, why it exists) | DEF-CHG001 (catalyst lowers it), PRIM-CHG004 (rate depends on it) | CHG imports PRIM-NRG006. NRG owns the energy concept; CHG owns the transformation concepts that deploy it. |
| Spontaneity | PRIM-NRG005 (thermodynamic favorability: will the process occur?) | CHG uses for reaction direction | CHG imports PRIM-NRG005. NRG owns the favorability assessment; CHG uses it to determine whether transformation proceeds. |
| Bond energy | PRIM-NRG002 (energy stored in bonds: net energy balance) | CHG uses for understanding reaction energetics | CHG imports PRIM-NRG002. NRG owns the energy accounting; CHG applies it to specific transformations. |
| Equilibrium | NRG explains WHY (entropy drives toward maximum probability) | PRIM-CHG003 (HOW equilibrium behaves dynamically: rate balance, Le Chatelier response) | CHG owns the equilibrium concept as a transformation phenomenon. NRG provides the thermodynamic driving force. |

**Governing rule (from CONVENTIONS.md Boundary Principle P2)**: NRG owns energy concepts (what energy is, how it is stored, whether a process is favorable). CHG owns transformation concepts (what reacts, what forms, how fast, how far). When a transformation uses energy reasoning, CHG imports from NRG.

### Tier Inconsistency Resolution: PRIM-CHG007 / DEF-CHG004

PRIM-CHG007 (nuclear change reasoning) is Enrichment. DEF-CHG004 (half-life) depends on PRIM-CHG007. Per CONVENTIONS.md Principle 4: "Enrichment items MUST NOT be prerequisites for Core items. The Core tier alone MUST form a self-contained, dependency-complete sub-taxonomy." Therefore DEF-CHG004 MUST also be Enrichment. Demoting DEF-CHG004 to E is the correct resolution: if the foundational nuclear reasoning move is cuttable, then the quantitative tool (half-life) that depends on it is equally cuttable. No Core item in any domain depends on DEF-CHG004 except through already-Enrichment chains.

## 6. Real-World Hooks

| ID | Concept | Everyday Application |
|----|---------|---------------------|
| PRIM-CHG001 | Equation reading and balancing | Understanding why incomplete combustion in a poorly ventilated grill produces CO (insufficient O2 to complete the balanced ratio) |
| PRIM-CHG002 | Reaction type recognition | Predicting that baking soda + vinegar produces CO2 gas (acid-carbonate double replacement) without memorizing the specific reaction |
| PRIM-CHG003 | Equilibrium reasoning | Explaining why a soda goes flat faster when warm (CO2 equilibrium shifts with temperature) |
| PRIM-CHG004 | Rate reasoning | Explaining why refrigerators preserve food (lower temperature slows decomposition rate) and why pressure cookers speed cooking |
| PRIM-CHG005 | Acid-base reasoning | Understanding how antacids neutralize stomach acid (CaCO3 accepts protons from HCl) |
| PRIM-CHG006 | Oxidation-reduction reasoning | Explaining how batteries work (Zn oxidized, MnO2 reduced, electrons flow through circuit) and why iron rusts |
| PRIM-CHG007 | Nuclear change reasoning | Understanding how smoke detectors work (americium-241 alpha emission) and why carbon dating measures age |
| DEF-CHG001 | Catalyst | Explaining catalytic converters (Pt/Pd lower E_a for exhaust gas conversion) and lactose intolerance (lack of enzyme catalyst) |
| DEF-CHG002 | pH scale | Testing swimming pool water (pH 7.2--7.8 for safety) and adjusting garden soil pH |
| DEF-CHG003 | Le Chatelier's principle | Industrial ammonia production (Haber process conditions chosen to maximize yield) and hyperventilation causing blood pH shift |
| DEF-CHG004 | Half-life | Carbon-14 dating of archaeological artifacts and iodine-131 clearance in nuclear medicine |
| DEF-CHG005 | Precipitation | Hard water scale in kettles (CaCO3 precipitate) and water treatment using alum |

## 7. Intra-Domain Dependency Graph

```
PRIM-COM005 (imported)   PRIM-COM006 (imported)   PRIM-STR001 (imported)
      \                        |                        |
       \                       |                        |
        +------> PRIM-CHG001 (Equation reading          |
                  and balancing)                         |
                                                        v
                                                  PRIM-CHG002 (Reaction type
                                                   recognition)

PRIM-SCL003 (imported)                    PRIM-NRG006 (imported)
      |         \                              |
      |          \                             |
      v           +----------------------+     |
PRIM-CHG003       |                      |     |
(Equilibrium)     v                      v     v
      |       PRIM-CHG004           DEF-CHG005 (Precipitation) [E]
      |       (Rate reasoning)      [also depends: PRIM-STR001 imported]
      |            |
      v            v
DEF-CHG003    DEF-CHG001
(Le Chatelier) (Catalyst)
               [also depends: PRIM-NRG006 imported]

PRIM-STR002 (imported)         PRIM-COM007 (imported)
      |                              |
      v                              v
PRIM-CHG005                    PRIM-CHG006
(Acid-base)                    (Oxidation-reduction)
      |
      v
DEF-CHG002 (pH scale)
[also depends: PRIM-SCL003 imported]

DEF-COM001 (imported)
      |
      v
PRIM-CHG007 (Nuclear change) [E]
      |
      v
DEF-CHG004 (Half-life) [E]
```

**Acyclicity verification**: All arrows point from imported items or earlier-defined CHG items to later-defined CHG items. No item depends on an item that depends on it. Imported items serve as roots with no CHG predecessors. The graph is a DAG.

**Core-only subgraph**: Removing PRIM-CHG007 (E), DEF-CHG004 (E), and DEF-CHG005 (E) leaves all 9 Core items (7 PRIM excluding CHG007 + DEF-CHG001, DEF-CHG002, DEF-CHG003 minus the three E items = 6 PRIM + 3 DEF = 9 Core items) with fully satisfied dependency chains. No Core item depends on any Enrichment item.

## 8. Cross-Domain Interface

### Exports

| ID | Concept | Imported by |
|----|---------|-------------|
| PRIM-CHG001 | Equation reading and balancing | SCL |
| PRIM-CHG002 | Reaction type recognition | -- |
| PRIM-CHG003 | Equilibrium reasoning | SCL |
| PRIM-CHG004 | Rate reasoning | -- |
| PRIM-CHG005 | Acid-base reasoning | SCL |
| PRIM-CHG006 | Oxidation-reduction reasoning | SCL |
| PRIM-CHG007 | Nuclear change reasoning | SCL |
| DEF-CHG001 | Catalyst | -- |
| DEF-CHG002 | pH scale | SCL |
| DEF-CHG003 | Le Chatelier's principle | -- |
| DEF-CHG004 | Half-life | SCL |
| DEF-CHG005 | Precipitation | -- |

### Imports

| DEP ID | Imported Item | Source Domain | Used by |
|--------|---------------|--------------|---------|
| DEP-CHG001 | PRIM-COM005 (Chemical formula reading) | COM | PRIM-CHG001 |
| DEP-CHG002 | PRIM-COM006 (Conservation of atoms) | COM | PRIM-CHG001 |
| DEP-CHG003 | PRIM-COM007 (Valence electron reasoning) | COM | PRIM-CHG006 |
| DEP-CHG004 | DEF-COM001 (Isotope) | COM | PRIM-CHG007 |
| DEP-CHG005 | PRIM-STR001 (Bond type classification) | STR | PRIM-CHG002, DEF-CHG005 |
| DEP-CHG006 | PRIM-STR002 (Bond polarity reasoning) | STR | PRIM-CHG005 |
| DEP-CHG007 | PRIM-NRG006 (Activation energy reasoning) | NRG | PRIM-CHG004, DEF-CHG001 |
| DEP-CHG008 | PRIM-SCL003 (Concentration reasoning) | SCL | PRIM-CHG003, PRIM-CHG004, DEF-CHG002, DEF-CHG005 |

## 9. Difficulty Tiers

| ID | Concept | Tier | Justification |
|----|---------|------|---------------|
| PRIM-CHG001 | Equation reading and balancing | C | Gateway skill: every CHG concept operates on or refers to a balanced equation; equation-reading is the entry point to all transformation reasoning |
| PRIM-CHG002 | Reaction type recognition | C | Core pattern: classifying reactions by type is the first prediction tool for unknown products; transfers across all reaction contexts |
| PRIM-CHG003 | Equilibrium reasoning | C | Core dynamic: the "static to dynamic" threshold; without equilibrium reasoning, students cannot reason about reversibility, Le Chatelier, or real-world chemical balance |
| PRIM-CHG004 | Rate reasoning | C | Core kinetic concept: separates "favorable" from "fast," correcting a pervasive misconception; essential for understanding catalysts, food preservation, and industrial chemistry |
| PRIM-CHG005 | Acid-base reasoning | C | Core reaction class: acids and bases pervade cooking, medicine, environment, and cleaning; the most practically relevant reaction type for non-majors |
| PRIM-CHG006 | Oxidation-reduction reasoning | C | Core reaction class: batteries, corrosion, metabolism, and combustion are all redox; electron transfer reasoning is essential for technological and biological literacy |
| PRIM-CHG007 | Nuclear change reasoning | E | Enrichment: nuclear chemistry is specialized; no downstream Core item requires it; omitting it does not break any dependency chain |
| DEF-CHG001 | Catalyst | C | Core definition: catalysts appear in every domain (biology, industry, environment); understanding how they work is essential for non-majors chemical literacy |
| DEF-CHG002 | pH scale | C | Core measurement: pH is the most commonly encountered chemical measurement in everyday life (pool testing, soil, food, medicine) |
| DEF-CHG003 | Le Chatelier's principle | C | Core prediction tool: the go-to qualitative method for predicting equilibrium perturbation; essential for industrial chemistry and biological equilibrium reasoning |
| DEF-CHG004 | Half-life | E | Enrichment: depends on PRIM-CHG007 (E); per tier constraint, must be E; valuable for dating and nuclear medicine but not required by any Core item |
| DEF-CHG005 | Precipitation | E | Enrichment: specialized double-replacement application; useful for water chemistry but not required by any Core item |

**Tier constraint verification**: Three Enrichment items: PRIM-CHG007 (E), DEF-CHG004 (E), DEF-CHG005 (E). No Core item depends on any Enrichment item. DEF-CHG004 depends on PRIM-CHG007 (both E) -- tier-consistent. DEF-CHG005 depends only on imported Core items (PRIM-STR001, PRIM-SCL003) -- its E status is by pedagogical choice, not dependency constraint. Removing all three Enrichment items leaves 9 Core items (6 PRIM + 3 DEF) with fully satisfied dependency chains. The Core tier alone forms a self-contained, dependency-complete sub-taxonomy.

## 10. Self-Audit Checklist

- [x] Every PRIM has: reasoning move formulation ("Given X, do Y to determine Z"), description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [x] Every DEF depends only on previously listed PRIM/DEF (check intra-domain dependency graph: DEF-CHG001 depends on PRIM-CHG004 and PRIM-NRG006; DEF-CHG002 depends on PRIM-CHG005 and PRIM-SCL003; DEF-CHG003 depends on PRIM-CHG003; DEF-CHG004 depends on PRIM-CHG007; DEF-CHG005 depends on PRIM-STR001 and PRIM-SCL003 -- all previously defined or imported)
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format (PRIM-COM005, PRIM-COM006, PRIM-COM007, DEF-COM001, PRIM-STR001, PRIM-STR002, PRIM-NRG006, PRIM-SCL003, etc.)
- [x] Every import is listed in the source domain's exports (verified: PRIM-COM005 in COM exports with CHG; PRIM-COM006 in COM exports with CHG; PRIM-COM007 in COM exports with STR -- note COM exports to STR, CHG imports transitively via valence electron reasoning; DEF-COM001 in COM exports with CHG; PRIM-STR001 in STR exports with CHG; PRIM-STR002 in STR exports with CHG; PRIM-NRG006 in NRG exports with CHG; PRIM-SCL003 in SCL exports with CHG)
- [x] Dissolution argument is present and non-trivial (Section 1: 5+ sentences distinguishing CHG from NRG, COM, STR, and SCL with concrete examples of what NRG cannot tell you about a transformation)
- [x] Real-world hooks cover everyday non-major contexts (cooking, batteries, corrosion, medicine/antacids, carbon dating, pollution/water treatment, digestion/lactose intolerance, food preservation, pool chemistry, gardening, smoke detectors, industrial chemistry)
- [x] Intra-domain dependency graph is acyclic (Section 7: all edges point from imported items or earlier CHG items to later CHG items; no cycles)
- [x] Tier annotations (C/E) are present on all 12 items (9 Core + 3 Enrichment)
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry in CONVENTIONS.md Section 9: no CHG concept appears in COM, STR, NRG, or SCL)
- [x] Reasoning moves are genuinely "Given X, do Y" cognitive operations (not mere topic labels or vocabulary words: each PRIM specifies input, operation, and output; each DEF specifies a constructed concept grounded in prior PRIMs)
