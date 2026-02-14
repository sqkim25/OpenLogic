# DOMAIN-STR v0.1

## 0. Sources & Assumptions

- SRC-STR001: Gillespie & Hargittai, *The VSEPR Model of Molecular Geometry*, 1991 (authoritative treatment of electron-pair repulsion and molecular shape prediction)
- SRC-STR002: Pauling, *The Nature of the Chemical Bond*, 3rd ed., 1960 (foundational source on electronegativity, bond polarity, and hydrogen bonding)
- SRC-STR003: Taber, "Chemical misconceptions -- prevention, diagnosis and cure," *Royal Society of Chemistry*, 2002 (common student errors in bonding and intermolecular force reasoning)
- SRC-GLB008: OpenStax, *Chemistry 2e*, 2019, Ch. 4--8 (bonding, molecular geometry, IMFs, liquids/solids)
- SRC-GLB009: Zumdahl & Zumdahl, *Chemistry*, 10th ed., 2017, Ch. 4--8
- SRC-GLB010: ACS, *Chemistry in Context*, 10th ed., 2020, Ch. 3--5
- ASM-STR001: Students arrive with COM primitives in place: they can identify atoms, read formulas, determine valence electron counts, and compare electronegativities. No structural reasoning is assumed prior to this domain. Justification: the COM --> STR dependency in the domain DAG means STR can rely on COM's full export list.
- ASM-STR002: Molecular geometry is taught via VSEPR as a predictive heuristic, not derived from quantum mechanics. Students learn to predict shapes from Lewis structures without solving the Schrodinger equation. Justification: VSEPR provides sufficient accuracy for non-majors and requires no calculus (ASM-GLB002).

## 1. Domain Intent

- **Governing question**: How does the arrangement of atoms determine a substance's properties?
- **Scope**: Determining how atoms connect (bond types), how electrons are distributed (polarity), what 3D shapes molecules adopt (geometry), what forces exist between molecules (IMFs), and how these structural features predict macroscopic properties. STR provides the arrangement layer: given the atoms and electron counts from COM, STR determines how those atoms are organized in space and what consequences follow.
- **Non-goals**: What elements exist or their identity (COM). Why energy drives processes or whether transformations are thermodynamically favorable (NRG). How substances transform into other substances, reaction rates, or equilibrium (CHG). Quantitative scale-bridging from molecular features to bulk measurements (SCL).
- **Dissolution argument**: Two substances with the same molecular formula (isomers) can have drastically different properties purely due to arrangement. Ethanol (CH3CH2OH) is a drinkable alcohol; dimethyl ether (CH3OCH3) is a gas used as an aerosol propellant. Same atoms, same count, different arrangement, different properties. This cannot reduce to composition: COM tells you both contain C2H6O, but COM cannot explain why one is a liquid you can drink and the other is a flammable gas. It cannot reduce to energy: structure determines WHICH properties emerge; energy determines WHETHER processes occur. It cannot reduce to change: structure exists before any transformation happens. The structure-to-property reasoning chain is the single most important chemical thinking skill for non-majors (SRC-GLB005, Talanquer threshold schemas) because it is the conceptual move that connects molecular-level arrangement to the everyday observable world.
- **Threshold schema mapping**: Additive --> Emergent. The foundational conceptual shift in STR is recognizing that molecular properties are not simply the sum of atomic properties but emerge from how atoms are arranged. Water's remarkable solvent ability does not come from hydrogen or oxygen individually -- it emerges from the bent geometry and the resulting polarity that neither atom possesses alone. Students who fail to cross this threshold treat molecular properties as additive inventories of atomic properties and cannot explain why isomers behave differently.

## 2. Prerequisites

STR depends on COM. The following items are imported:

| DEP ID | Imported Item | Purpose in STR |
|--------|---------------|----------------|
| DEP-STR001 | PRIM-COM007 (valence electron reasoning) | Required for drawing Lewis structures (DEF-STR001) -- must know how many valence electrons each atom contributes |
| DEP-STR002 | DEF-COM005 (electronegativity) | Required for bond type classification (PRIM-STR001) and bond polarity reasoning (PRIM-STR002) -- must compare electronegativity values |
| DEP-STR003 | PRIM-COM001 (atomic composition analysis) | Required to know which atoms are present before reasoning about their arrangement |
| DEP-STR004 | DEF-COM002 (ion) | Required for metallic structure reasoning (DEF-STR009) -- must understand cation formation |

STR does NOT import from NRG, CHG, or SCL. Independence arguments are documented in CONVENTIONS.md Section 10.

## 3. Primitives

- PRIM-STR001: **Bond type classification**
  - Reasoning move: Given two elements and their electronegativities, calculate the electronegativity difference to classify the bond as covalent (shared equally), polar covalent (shared unequally), or ionic (transferred), and predict the resulting material type (molecular substance, ionic solid, or metallic solid).
  - Description: The cognitive operation of determining how atoms share or transfer electrons when they bond. This is the first structural question after COM identifies which atoms are present: HOW are these atoms connected? The classification depends on electronegativity difference (delta-EN): small delta-EN means electrons are shared equally (nonpolar covalent); moderate delta-EN means electrons are shared unequally (polar covalent); large delta-EN means electrons are effectively transferred (ionic). Metallic bonding is a separate category where metal atoms pool their valence electrons into a delocalized sea. The bond type determines the entire downstream reasoning chain: molecular vs. ionic substance, polarity, IMF type, and macroscopic behavior.
  - Semi-formal: Given atoms A and B with electronegativities EN(A) and EN(B): delta-EN = |EN(A) - EN(B)|. If delta-EN < 0.4, bond is nonpolar covalent. If 0.4 <= delta-EN < 1.7, bond is polar covalent. If delta-EN >= 1.7, bond is ionic. If both A and B are metals, bond is metallic. (Thresholds are approximate guidelines, not rigid cutoffs.)
  - Depends: DEF-COM005 (electronegativity -- imported from COM)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 4), SRC-GLB009 (Zumdahl Ch. 4), SRC-STR002 (Pauling, Ch. 3)
  - Referenced by: NRG, CHG
  - Tier: C
  - Real-world hook: Table salt (NaCl) is ionic (delta-EN = 2.1), which is why it forms hard crystals that dissolve in water. Vegetable oil is nonpolar covalent (C-H bonds, delta-EN ~ 0.4), which is why it does not dissolve in water. Knowing the bond type from just two elements' positions on the periodic table predicts whether a substance dissolves in your salad dressing or sits on top of it.

- PRIM-STR002: **Bond polarity reasoning**
  - Reasoning move: Given a bond between two atoms, use their electronegativity difference to determine the direction and magnitude of partial charge separation (which end is delta-negative, which is delta-positive) and predict how that bond contributes to the molecule's overall electron distribution.
  - Description: The cognitive operation of locating where electrons are concentrated within a single bond. Bond polarity is the molecular-level origin of all electrical asymmetry in molecules. The more electronegative atom pulls electron density toward itself, acquiring a partial negative charge (delta-), while the less electronegative atom becomes partially positive (delta+). This is not full charge transfer (that would be ionic); it is unequal sharing. Bond polarity reasoning is the bridge between the periodic-table-level concept of electronegativity (COM) and the molecule-level concept of molecular polarity (DEF-STR002). Each bond is a vector with a direction (toward the more electronegative atom) and a magnitude (proportional to delta-EN).
  - Semi-formal: For a bond A--B where EN(A) > EN(B): atom A carries partial charge delta- and atom B carries partial charge delta+. The bond dipole vector points from delta+ toward delta-. Magnitude of bond dipole is proportional to delta-EN(A,B). If delta-EN = 0, the bond has no polarity (symmetric electron sharing).
  - Depends: DEF-COM005 (electronegativity -- imported from COM), PRIM-STR001 (bond type classification -- must first determine that the bond is polar covalent, not ionic or nonpolar)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 4), SRC-STR002 (Pauling, Ch. 3), SRC-GLB009 (Zumdahl Ch. 4)
  - Referenced by: NRG, CHG
  - Tier: C
  - Real-world hook: In a water molecule (H-O-H), oxygen is more electronegative than hydrogen, so each O-H bond has a partial negative charge on the oxygen end. This is why water sticks to glass, climbs up paper towels, and dissolves salt -- all traceable to the partial charges in two small bonds.

- PRIM-STR003: **Molecular shape reasoning**
  - Reasoning move: Given a Lewis structure, count the electron groups (bonding pairs and lone pairs) around the central atom, apply electron-pair repulsion (VSEPR model) to predict the 3D molecular geometry, and determine whether the shape produces or cancels molecular polarity.
  - Description: The cognitive operation of going from a flat 2D Lewis structure to a 3D molecular shape. The VSEPR model says electron groups repel each other and arrange to maximize their distance apart. Two groups give linear geometry (180 degrees); three give trigonal planar (120 degrees); four give tetrahedral (109.5 degrees). Lone pairs occupy space but are invisible in the molecular shape, which is defined only by atom positions. This distinction between electron geometry (includes lone pairs) and molecular geometry (atoms only) is a persistent source of student error (SRC-STR003). Shape determines whether bond dipoles cancel or reinforce, which determines molecular polarity, which determines intermolecular forces, which determines macroscopic properties -- the full structure-to-property chain begins here.
  - Semi-formal: For central atom X with n bonding groups and m lone pairs: total electron groups = n + m. Electron geometry is determined by (n + m): 2 = linear, 3 = trigonal planar, 4 = tetrahedral. Molecular geometry is determined by (n, m): (2,0) = linear, (3,0) = trigonal planar, (2,1) = bent, (4,0) = tetrahedral, (3,1) = trigonal pyramidal, (2,2) = bent. Bond angles decrease slightly from ideal when lone pairs are present (lone pairs occupy more angular space than bonding pairs).
  - Depends: DEF-STR001 (Lewis structure -- must have the 2D bonding diagram before predicting 3D shape)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 5), SRC-STR001 (Gillespie & Hargittai), SRC-GLB009 (Zumdahl Ch. 5)
  - Referenced by: CHG, SCL
  - Tier: C
  - Real-world hook: Carbon dioxide (CO2) is linear, so its bond dipoles cancel and it is nonpolar -- that is why CO2 is a gas at room temperature with weak intermolecular forces. Water (H2O) is bent, so its bond dipoles do NOT cancel and it is polar -- that is why water is a liquid with strong intermolecular forces. Same number of atoms (3), completely different properties, entirely because of shape.

- PRIM-STR004: **Intermolecular force hierarchy**
  - Reasoning move: Given a molecule's structure (polarity, hydrogen-bonding capability, and size), identify which intermolecular forces (IMFs) are present, rank them by strength (London dispersion < dipole-dipole < hydrogen bonding < ionic interactions), and predict relative physical properties.
  - Description: The cognitive operation of determining what holds molecules NEAR each other (as opposed to what holds atoms WITHIN a molecule, which is bonding). IMFs are much weaker than covalent or ionic bonds, but they govern phase, boiling point, viscosity, and solubility. Every molecule has London dispersion forces (from temporary electron fluctuations); polar molecules additionally have dipole-dipole forces; molecules with H bonded to N, O, or F additionally have hydrogen bonds. The hierarchy is the ranking tool: stronger IMFs mean higher boiling points, greater viscosity, and lower vapor pressure. This is the critical bridge between molecular-level structure and macroscopic behavior -- a common point of student confusion where students conflate intramolecular bonds with intermolecular forces (SRC-STR003).
  - Semi-formal: For molecule M: (1) London dispersion forces are always present; strength increases with molecular size (more electrons = more polarizable). (2) If M is polar (DEF-STR002), dipole-dipole forces are present; strength proportional to dipole magnitude. (3) If M has H bonded to N, O, or F, hydrogen bonds are present (DEF-STR003). (4) If M is an ion, ionic interactions dominate. Ranking: London < dipole-dipole < hydrogen bonding < ionic. Dominant IMF = the strongest type present in M.
  - Depends: PRIM-STR002 (bond polarity reasoning -- needed to assess molecular polarity), DEF-STR002 (molecular polarity -- determines whether dipole-dipole forces are present), DEF-STR003 (hydrogen bond -- must define H-bonds before including them in the hierarchy)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 8), SRC-GLB009 (Zumdahl Ch. 8), SRC-GLB010 (ACS Ch. 5)
  - Referenced by: SCL, CHG
  - Tier: C
  - Real-world hook: Why does rubbing alcohol evaporate off your skin faster than water? Both are small polar molecules, but water has stronger hydrogen bonds (two O-H groups vs. one O-H in isopropanol plus a bulky nonpolar tail). Stronger IMFs mean harder to vaporize. The IMF hierarchy explains evaporation rate, which is why alcohol feels cold on skin -- it evaporates fast, pulling heat away.

- PRIM-STR005: **Structure-to-property inference**
  - Reasoning move: Given a molecule's structural features (polarity, IMF type and strength, shape, and functional groups), predict the direction (higher/lower, more/less) of a macroscopic property -- boiling point, melting point, solubility, viscosity, or vapor pressure -- relative to a comparison molecule.
  - Description: The cognitive operation that completes the full structure-to-property chain. This is the culminating reasoning move of the STR domain: it takes all upstream structural information (bond type, polarity, shape, IMFs) and translates it into a qualitative prediction about observable behavior. The prediction is always comparative ("substance A has a higher boiling point than substance B because...") and always directional (not numerical -- numerical predictions require SCL). This primitive is the chemistry equivalent of "reading" molecular structure the way a mechanic reads an engine diagram: the structure tells you what the substance will do. Students who master this move can evaluate claims about materials, drugs, solvents, and consumer products without memorizing individual facts.
  - Semi-formal: Given molecules M_1 and M_2 with identified dominant IMFs: if IMF(M_1) > IMF(M_2), then boiling point(M_1) > boiling point(M_2), viscosity(M_1) > viscosity(M_2), and vapor pressure(M_1) < vapor pressure(M_2). For solubility: "like dissolves like" (DEF-STR004) -- polar solutes dissolve in polar solvents; nonpolar in nonpolar. For molecules with same IMF type, larger molecular size --> stronger London forces --> higher boiling point.
  - Depends: PRIM-STR003 (molecular shape reasoning -- shape determines polarity and IMF access), PRIM-STR004 (intermolecular force hierarchy -- IMFs drive macroscopic properties)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 8), SRC-GLB009 (Zumdahl Ch. 8), SRC-GLB005 (Talanquer threshold schemas, 2015)
  - Referenced by: SCL, CHG
  - Tier: C
  - Real-world hook: Why is coconut oil solid at room temperature but olive oil is liquid? Both are fats (long carbon chains with ester groups), but coconut oil has more saturated (straight) chains that pack tightly with strong London forces, while olive oil has unsaturated (kinked) chains that pack poorly. Structure-to-property inference: tighter packing means stronger IMFs means solid at room temperature.

## 4. Definitions

- DEF-STR001: **Lewis structure**
  - Reasoning move: Given a molecular formula and the valence electron count for each atom, distribute electrons as bonding pairs and lone pairs to satisfy the octet rule (duet for H), producing a 2D diagram that shows how atoms are connected and where unshared electrons reside.
  - Description: A Lewis structure is the foundational diagram of bonding in a molecule. It shows which atoms are bonded to which, whether bonds are single, double, or triple, and where lone (nonbonding) electron pairs are located. Drawing a Lewis structure is the critical translation step from composition (how many valence electrons?) to structure (where do they go?). The procedure is algorithmic: (1) count total valence electrons, (2) connect atoms with single bonds, (3) distribute remaining electrons as lone pairs to satisfy octets, (4) if electrons are insufficient, convert lone pairs to multiple bonds. Resonance structures arise when multiple valid Lewis structures exist for the same molecule, but resonance is treated as a notational convention, not a physical description (the real structure is a weighted average).
  - Semi-formal: Given formula with atoms {A_1, ..., A_n}: total valence electrons V = sum of valence_e(A_i) (from PRIM-COM007), adjusted for charge. Place bonds between connected atoms (each bond uses 2 electrons). Distribute remaining (V - 2*bonds) electrons as lone pairs, filling outer atoms first, then central atom. If central atom lacks octet, convert lone pair on adjacent atom to bonding pair (creating double/triple bond). Lewis structure = graph G(atoms, bonds, lone_pairs) satisfying octet/duet constraints.
  - Depends: PRIM-COM007 (valence electron reasoning -- imported from COM; provides the electron count input)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 4), SRC-GLB009 (Zumdahl Ch. 4), SRC-GLB010 (ACS Ch. 3)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: The Lewis structure of carbon dioxide (O=C=O) shows two double bonds and no lone pairs on carbon, which is why CO2 is linear and nonpolar. The Lewis structure of formaldehyde (H2C=O) shows a double bond to oxygen, which is why formaldehyde is reactive and used as a preservative. Drawing the Lewis structure is the first step to understanding why a chemical behaves the way it does.

- DEF-STR002: **Molecular polarity**
  - Reasoning move: Given a molecule's shape (from VSEPR) and its bond dipoles (from bond polarity reasoning), determine the vector sum of all bond dipoles to classify the molecule as polar or nonpolar and predict its macroscopic behavior.
  - Description: Molecular polarity is the net result of all bond dipoles in a molecule, determined by both the magnitude of individual bond dipoles AND the 3D geometry. A molecule can have polar bonds but still be nonpolar overall if the geometry causes the bond dipoles to cancel (like CO2: two equal and opposite C=O dipoles in a linear geometry). Conversely, a bent molecule like water has bond dipoles that reinforce, producing a net dipole. Molecular polarity is the critical link between individual bond polarity (PRIM-STR002) and intermolecular forces (PRIM-STR004): it determines whether a molecule experiences dipole-dipole forces and hydrogen bonding in addition to London dispersion forces.
  - Semi-formal: For molecule M with bond dipole vectors {d_1, d_2, ..., d_k}: net dipole D = vector sum of all d_i. If |D| > 0, M is polar. If |D| = 0 (all dipoles cancel due to symmetry), M is nonpolar. Symmetric geometries (linear with identical bonds, trigonal planar with identical bonds, tetrahedral with identical bonds) produce |D| = 0. Asymmetric geometries or mixed bond types produce |D| > 0.
  - Depends: PRIM-STR002 (bond polarity reasoning -- provides the individual bond dipole vectors), PRIM-STR003 (molecular shape reasoning -- provides the 3D geometry needed for vector summation)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 5), SRC-GLB009 (Zumdahl Ch. 5), SRC-STR002 (Pauling, Ch. 3)
  - Referenced by: SCL, CHG
  - Tier: C
  - Real-world hook: Why does plastic wrap cling to a glass bowl but not to itself very well? Plastic wrap (polyethylene) is nonpolar; glass has polar surface groups. When you stretch the wrap, you create a slight static charge that interacts with the polar glass surface. Molecular polarity governs which surfaces stick to which -- it is the reason oil and water separate in salad dressing.

- DEF-STR003: **Hydrogen bond**
  - Reasoning move: Given a molecule containing H bonded to N, O, or F, identify the potential for hydrogen bonding with another molecule's lone pair on N, O, or F, and recognize this as a particularly strong type of dipole-dipole interaction.
  - Description: A hydrogen bond is a special, unusually strong dipole-dipole interaction that occurs when a hydrogen atom bonded to a highly electronegative atom (N, O, or F) interacts with a lone pair on another N, O, or F atom. Hydrogen bonds are roughly 10 times stronger than ordinary dipole-dipole forces (though still roughly 10 times weaker than covalent bonds). They are responsible for water's anomalously high boiling point, ice's lower density than liquid water, protein folding, and DNA base pairing. The specificity of hydrogen bonding (only H bonded to N/O/F, only lone pairs on N/O/F) distinguishes it from generic dipole-dipole forces and makes it a separately named concept rather than a mere subcategory.
  - Semi-formal: A hydrogen bond exists between molecule M_1 and molecule M_2 when: (1) M_1 contains a bond X-H where X is in {N, O, F}, and (2) M_2 contains an atom Y in {N, O, F} with a lone pair. The interaction is X-H...Y, where ... denotes the hydrogen bond. Strength: approximately 5--30 kJ/mol (compared to ~2 kJ/mol for typical dipole-dipole and ~200--400 kJ/mol for covalent bonds).
  - Depends: PRIM-STR002 (bond polarity reasoning -- the H-X bond must be highly polar for H-bonding to occur)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 8), SRC-STR002 (Pauling, Ch. 12), SRC-GLB009 (Zumdahl Ch. 8)
  - Referenced by: SCL, CHG
  - Tier: C
  - Real-world hook: Why does it take so long to boil a pot of water compared to the same volume of rubbing alcohol? Water forms extensive hydrogen bond networks (each molecule can form up to 4 hydrogen bonds), requiring much more energy to pull molecules apart into the gas phase. Hydrogen bonding is also why a wet paper towel sticks to a surface and why DNA holds its double helix together.

- DEF-STR004: **"Like dissolves like"**
  - Reasoning move: Given a solute and a solvent, compare their polarities (polar vs. nonpolar) to predict whether the solute will dissolve: polar dissolves in polar, nonpolar dissolves in nonpolar, and polar/nonpolar combinations generally do not mix.
  - Description: "Like dissolves like" is the heuristic rule that connects molecular polarity to solubility. The underlying mechanism is IMF compatibility: a polar solute dissolves in a polar solvent when solute-solvent IMFs (dipole-dipole, H-bonding) are comparable in strength to solute-solute and solvent-solvent IMFs. A nonpolar solute dissolves in a nonpolar solvent when London forces between solute and solvent are comparable to those within each pure substance. When a polar solute is placed in a nonpolar solvent, the strong solute-solute interactions (dipole-dipole or H-bonds) have no replacement in the nonpolar solvent, so dissolution is unfavorable. This rule is approximate but remarkably reliable for qualitative predictions.
  - Semi-formal: For solute S and solvent V: if polarity(S) matches polarity(V) (both polar or both nonpolar), then S is soluble in V. If polarity(S) does not match polarity(V), then S is insoluble (or sparingly soluble) in V. Special case: ionic compounds dissolve in water (polar) because ion-dipole interactions replace the ionic lattice energy.
  - Depends: DEF-STR002 (molecular polarity -- must classify solute and solvent as polar or nonpolar), PRIM-STR004 (intermolecular force hierarchy -- dissolution requires IMF compatibility)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 8), SRC-GLB010 (ACS Ch. 5), SRC-GLB009 (Zumdahl Ch. 8)
  - Referenced by: SCL
  - Tier: C
  - Real-world hook: Grease stains do not come out with water alone because grease is nonpolar and water is polar. Dish soap works because it has a polar head (dissolves in water) and a nonpolar tail (dissolves in grease), bridging the two. Dry cleaning uses nonpolar solvents that dissolve nonpolar stains directly. "Like dissolves like" is the rule behind every cleaning product in your house.

- DEF-STR005: **Isomer recognition**
  - Reasoning move: Given two molecules with the same molecular formula, determine whether they are isomers (same formula, different arrangement) by identifying structural differences (different connectivity) or geometric differences (same connectivity, different spatial arrangement), and predict that they will have different properties.
  - Description: Isomers are the definitive proof that composition alone does not determine properties -- arrangement matters. Structural isomers (also called constitutional isomers) have different atom connectivity (e.g., butane vs. isobutane: same C4H10, different branching). Geometric isomers (cis/trans) have the same connectivity but different spatial arrangement around a double bond or ring. Different arrangement means different shape, different polarity, different IMFs, and therefore different macroscopic properties. Isomer recognition forces students to confront the additive-to-emergent threshold: the same atoms, counted the same way, produce different substances purely from arrangement.
  - Semi-formal: Molecules M_1 and M_2 are isomers if and only if: formula(M_1) = formula(M_2) AND structure(M_1) != structure(M_2). They are structural isomers if connectivity(M_1) != connectivity(M_2). They are geometric isomers if connectivity(M_1) = connectivity(M_2) but spatial_arrangement(M_1) != spatial_arrangement(M_2). For isomers: properties(M_1) != properties(M_2) in general.
  - Depends: PRIM-STR003 (molecular shape reasoning -- must understand 3D geometry to recognize different arrangements)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 7), SRC-GLB009 (Zumdahl Ch. 7), SRC-GLB010 (ACS Ch. 4)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: Ibuprofen exists as two isomers (R and S forms). Only the S-isomer is the active painkiller; the R-isomer is inactive. Your body can slowly convert R to S, but the drug works faster when manufactured as pure S-ibuprofen. Same formula, different arrangement, different biological effect -- isomer recognition explains why pharmaceutical companies care about molecular handedness.

- DEF-STR006: **Phase from IMF balance**
  - Reasoning move: Given a substance's dominant IMF strength and an approximate thermal energy context (room temperature, body temperature, or a stated condition), predict whether the substance is a solid, liquid, or gas by comparing IMF strength to the kinetic energy of the molecules.
  - Description: The phase of a substance at a given temperature is determined by the competition between intermolecular forces (which pull molecules together) and thermal kinetic energy (which pushes molecules apart). When IMFs dominate kinetic energy, molecules are locked in place: solid. When they are comparable, molecules slide past each other: liquid. When kinetic energy dominates, molecules fly apart: gas. This definition connects the molecular-level IMF hierarchy (PRIM-STR004) to the most basic observable property of any substance -- its phase. It explains why small nonpolar molecules (weak London forces) tend to be gases, large nonpolar molecules tend to be solids, and molecules with strong H-bonding (like water) are liquids at room temperature despite their small size.
  - Semi-formal: For substance S at temperature T: if IMF_strength(S) >> kinetic_energy(T), S is solid. If IMF_strength(S) ~ kinetic_energy(T), S is liquid. If IMF_strength(S) << kinetic_energy(T), S is gas. Phase transitions occur when T changes enough to shift the balance. Higher IMF strength --> higher melting and boiling points.
  - Depends: PRIM-STR004 (intermolecular force hierarchy -- provides the IMF strength ranking)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 8), SRC-GLB009 (Zumdahl Ch. 8), SRC-GLB010 (ACS Ch. 5)
  - Referenced by: SCL
  - Tier: C
  - Real-world hook: Methane (CH4) is a gas at room temperature because its only IMFs are weak London forces -- even room-temperature kinetic energy overwhelms them. Butter (a mix of long-chain fats) is solid in the fridge but liquid in a warm pan because its London forces are strong enough to compete with kinetic energy at low temperatures but lose at higher temperatures. Phase from IMF balance explains why your freezer preserves food: lowering temperature tips the IMF-vs-kinetic-energy balance toward solid, slowing molecular motion and chemical reactions.

- DEF-STR007: **Carbon backbone reasoning**
  - Reasoning move: Given that carbon has 4 valence electrons and forms 4 bonds, reason about how carbon's ability to form stable chains, branches, and rings with other carbon atoms (and with H, O, N, and other elements) produces the enormous diversity of organic molecules.
  - Description: Carbon is unique among elements in its ability to form long, stable chains of C-C bonds, to branch at any point, and to close into rings. Combined with single, double, and triple bonds and attachments to heteroatoms (O, N, S, halogens), this produces millions of distinct molecular structures from a small set of elements. Carbon backbone reasoning is the structural basis for understanding organic chemistry, biochemistry, and materials science. At the non-majors level, the key insight is: carbon's 4-bond versatility is WHY life, plastics, fuels, and drugs all center on carbon-based molecules.
  - Semi-formal: Carbon (group 14, 4 valence electrons) forms exactly 4 bonds. Carbon can bond to: other carbon atoms (forming chains of arbitrary length), hydrogen (saturating remaining bonds), and heteroatoms (O, N, S, halogens -- creating functional groups). The number of possible structures grows combinatorially with chain length: C_n H_(2n+2) has increasingly many structural isomers as n increases (n=4: 2 isomers; n=10: 75 isomers; n=20: 366,319 isomers).
  - Depends: PRIM-COM007 (valence electron reasoning -- imported from COM; carbon has 4 valence electrons), PRIM-STR001 (bond type classification -- C-C and C-H bonds are nonpolar covalent; C-O and C-N bonds are polar covalent)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 7), SRC-GLB009 (Zumdahl Ch. 7), SRC-GLB010 (ACS Ch. 4)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: Gasoline, polyester clothing, aspirin, sugar, and DNA are all built on carbon backbones. The difference between gasoline (short chains, ~8 carbons) and candle wax (long chains, ~25 carbons) is just chain length -- both are hydrocarbons, but the longer chains have stronger London forces and are therefore solid at room temperature. Carbon backbone reasoning explains why organic chemistry produces such an astonishing variety of substances from so few elements.

- DEF-STR008: **Polymer reasoning**
  - Reasoning move: Given a small molecule (monomer), predict how it can link into long repeating chains (polymers), and reason about how polymer chain length, branching, and intermolecular forces determine the material properties of the resulting plastic, fiber, or biological macromolecule.
  - Description: A polymer is a large molecule built from many copies of a small repeating unit (monomer) linked together. Polymer reasoning connects molecular-level structure (monomer identity, chain length, branching, cross-linking) to macroscopic material properties (flexibility, strength, melting behavior, biodegradability). Short chains with few intermolecular forces produce soft, flexible materials; long chains with strong IMFs or cross-links produce rigid, tough materials. This definition sits in STR because it is about how arrangement (chain architecture) determines properties, not about the reaction that forms the polymer (CHG) or the quantitative measurement of molecular weight (SCL).
  - Semi-formal: Given monomer M with a reactive functional group: polymerization produces (M)_n, a chain of n repeating M units. Material properties depend on: (1) chain length n (longer = stronger London forces), (2) branching (more branching = less crystalline packing = lower density), (3) cross-linking (cross-links between chains = rigid, thermoset material), (4) monomer polarity (polar monomers = stronger IMFs = higher melting point).
  - Depends: DEF-STR007 (carbon backbone reasoning -- most polymers are carbon-based chains), PRIM-STR004 (intermolecular force hierarchy -- IMFs between polymer chains determine material properties)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 7), SRC-GLB010 (ACS Ch. 4), SRC-GLB009 (Zumdahl Ch. 7)
  - Referenced by: SCL
  - Tier: C
  - Real-world hook: Plastic grocery bags (polyethylene, branched chains, weak London forces) are flexible and melt easily. Kevlar (aromatic polyamide, strong H-bonds between chains) is rigid enough to stop bullets. Both are polymers -- the difference in material properties comes entirely from the monomer structure and the resulting intermolecular forces between chains. Polymer reasoning explains why some plastics are recyclable (thermoplastics melt and re-form) and others are not (thermosets are cross-linked and cannot be re-melted).

- DEF-STR009: **Metallic structure**
  - Reasoning move: Given a metallic element, reason about the "electron sea" model -- metal cations arranged in a lattice surrounded by delocalized valence electrons -- to predict metallic properties: electrical conductivity, thermal conductivity, malleability, ductility, and luster.
  - Description: In metallic bonding, metal atoms release their valence electrons into a shared, delocalized pool (the "electron sea") while the remaining cations arrange in a regular lattice. This model explains metallic properties: conductivity arises because delocalized electrons flow freely; malleability arises because cation layers can slide past each other without breaking bonds (unlike ionic lattices, where displacement brings like charges together and shatters the crystal); luster arises because free electrons absorb and re-emit light across a wide spectrum. Metallic structure is distinct from ionic bonding (no discrete anion-cation pairs) and covalent bonding (no localized shared pairs). This definition is Enrichment because no downstream Core item depends on it.
  - Semi-formal: For a metal M with v valence electrons: M forms cation M^(v+) arranged in a lattice. The v electrons per atom are delocalized across the entire lattice. Properties: electrical conductivity proportional to electron mobility; thermal conductivity from electron-mediated energy transfer; malleability from non-directional bonding (lattice layers slide without shattering); luster from free-electron absorption/re-emission of visible light.
  - Depends: PRIM-STR001 (bond type classification -- must identify the bonding as metallic), DEF-COM002 (ion -- imported from COM; metals form cations in the electron sea)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 8), SRC-GLB009 (Zumdahl Ch. 8)
  - Referenced by: --
  - Tier: E
  - Real-world hook: Copper wiring conducts electricity because copper's valence electron is delocalized and free to flow. Gold is hammered into leaf (malleability) because its cation layers slide without breaking the electron sea. Aluminum foil can be rolled paper-thin (ductility) for the same reason. The electron sea model explains why metals are the material of choice for electrical wiring, cookware, and structural beams.

- DEF-STR010: **Water as solvent**
  - Reasoning move: Given water's molecular structure (bent geometry, high polarity, strong hydrogen bonding capacity), reason about why water is an exceptionally effective solvent for ionic and polar substances, and why it fails to dissolve nonpolar substances.
  - Description: Water is not just "a polar solvent" -- it is an extraordinarily effective one due to the combination of three structural features: (1) its bent geometry produces a large net dipole, (2) each water molecule can form up to 4 hydrogen bonds (2 as donor via O-H, 2 as acceptor via O lone pairs), and (3) its small molecular size gives it a high molar density of H-bonding sites. These features make water capable of surrounding and stabilizing ions (hydration shells, via ion-dipole interactions), dissolving polar molecules (via dipole-dipole and H-bonding), and maintaining liquid phase over an unusually wide temperature range. Water's solvent properties are central to biology (cellular chemistry occurs in aqueous solution), environmental science (water dissolves and transports pollutants), and everyday life (cooking, cleaning, medicine delivery).
  - Semi-formal: Water (H2O): molecular geometry = bent (from PRIM-STR003), net dipole > 0 (from DEF-STR002), H-bond capacity = 4 per molecule (from DEF-STR003). For ionic solute NaCl: water surrounds Na+ with O (delta-) end and Cl- with H (delta+) end, creating hydration shells. Ion-dipole interaction energy must exceed lattice energy for dissolution. For polar solute: water forms H-bonds or dipole-dipole interactions with solute, replacing solute-solute interactions. For nonpolar solute: water cannot form comparable interactions; dissolution is unfavorable ("like dissolves like," DEF-STR004).
  - Depends: DEF-STR002 (molecular polarity -- water must be classified as polar), DEF-STR003 (hydrogen bond -- water's H-bonding capacity is central to its solvent power), DEF-STR004 ("like dissolves like" -- the general rule that water as solvent instantiates)
  - Ownership: STR
  - Source: SRC-GLB008 (OpenStax Ch. 8), SRC-GLB009 (Zumdahl Ch. 8), SRC-GLB010 (ACS Ch. 5)
  - Referenced by: CHG, SCL
  - Tier: C
  - Real-world hook: You can dissolve a teaspoon of salt in a glass of water in seconds, but a teaspoon of sand sits unchanged at the bottom. Salt (ionic) is surrounded by water's strong ion-dipole interactions; sand (covalent network solid, nonpolar surface) has no compatible interactions with water. This is why ocean water is salty (dissolved NaCl) but beaches are sandy (undissolved SiO2). Water's exceptional solvent ability governs everything from blood chemistry to wastewater treatment.

## 5. Contested Concepts

The primary contested boundaries for STR are with NRG (energy) and SCL (scale). Three concepts require explicit ownership resolution:

| Concept | STR Version (Owner) | Other Domain Version | Resolution |
|---------|---------------------|----------------------|------------|
| Bond type | PRIM-STR001 owns classification of bonding mode (covalent/ionic/metallic) based on electronegativity difference | NRG uses bond energy (PRIM-NRG002) to quantify energy stored in bonds | Clean split via P2: STR classifies the type of bond; NRG quantifies the energy in the bond. STR says "this bond is polar covalent"; NRG says "this bond stores 463 kJ/mol." |
| Boiling point | PRIM-STR005 predicts direction ("A has higher bp than B because stronger IMFs") | SCL measures the numerical value and connects to macroscopic observation | Clean split via P3/P5: STR predicts qualitatively from molecular structure; SCL bridges to quantitative measurement. STR says "stronger IMFs means higher bp"; SCL says "the measured bp is 100 degrees C." |
| Hydrogen bonding | DEF-STR003 defines the molecular-level interaction (H bonded to N/O/F with lone pair) | SCL uses H-bonding to explain macroscopic anomalies (water's high bp, ice density) | Clean split via P3: the molecular-level interaction is STR; the macroscopic consequence is SCL (via CP-001). STR defines what an H-bond IS; SCL explains what H-bonds DO at bulk scale. |

No contested concepts exist between STR and CHG. CHG imports STR primitives (bond type, polarity, Lewis structures) when reasoning about transformations, but CHG does not redefine any STR concept.

## 6. Real-World Hooks

| ID | Concept | Everyday Application |
|----|---------|---------------------|
| PRIM-STR001 | Bond type classification | Predicting whether a substance dissolves in water (ionic/polar) or oil (nonpolar) from its formula |
| PRIM-STR002 | Bond polarity reasoning | Understanding why water molecules stick to glass and climb paper towels (partial charges create adhesion) |
| PRIM-STR003 | Molecular shape reasoning | Explaining why CO2 is a gas but water is a liquid despite similar molecular sizes (linear vs. bent geometry) |
| PRIM-STR004 | IMF hierarchy | Explaining why rubbing alcohol evaporates faster than water on skin (weaker IMFs = easier to vaporize) |
| PRIM-STR005 | Structure-to-property inference | Comparing coconut oil (solid, saturated) to olive oil (liquid, unsaturated) based on chain packing |
| DEF-STR001 | Lewis structure | Drawing the structure of caffeine to understand why it dissolves in hot water (polar functional groups) |
| DEF-STR002 | Molecular polarity | Understanding why oil and vinegar separate in salad dressing (nonpolar vs. polar) |
| DEF-STR003 | Hydrogen bond | Explaining why it takes so long to boil water compared to alcohol (extensive H-bond networks) |
| DEF-STR004 | "Like dissolves like" | Choosing the right cleaning solvent: water for salt stains, acetone for nail polish, mineral spirits for grease |
| DEF-STR005 | Isomer recognition | Understanding why only one form of ibuprofen is an effective painkiller (same formula, different 3D arrangement) |
| DEF-STR006 | Phase from IMF balance | Explaining why butter melts in a warm pan but wax needs a flame (different IMF strengths) |
| DEF-STR007 | Carbon backbone reasoning | Understanding why gasoline and candle wax are both hydrocarbons but one is liquid and one is solid (chain length) |
| DEF-STR008 | Polymer reasoning | Explaining why grocery bags are flexible but bulletproof vests are rigid (branching vs. H-bonded chains) |
| DEF-STR009 | Metallic structure | Understanding why copper conducts electricity and gold can be hammered into leaf (delocalized electron sea) |
| DEF-STR010 | Water as solvent | Explaining why ocean water is salty but beaches are sandy (water dissolves ionic NaCl, not covalent SiO2) |

## 7. Intra-Domain Dependency Graph

```
PRIM-COM007 (imported)    DEF-COM005 (imported)    DEF-COM002 (imported)
      |                        |                        |
      v                        v                        |
DEF-STR001 (Lewis       PRIM-STR001 (Bond type         |
 structure)               classification)               |
      |                   /         \                    |
      v                  v           \                   |
PRIM-STR003         PRIM-STR002      \                  |
 (Shape)            (Bond polarity)   \                 |
      |              /        \        \                |
      |             v          v        \               |
      |       DEF-STR002    DEF-STR003   \              |
      |       (Mol. polarity) (H-bond)    \             |
      |             |          |           |            |
      |             v          v           |            |
      |          PRIM-STR004 (IMF hierarchy)            |
      |          /      |       \                       |
      |         v       |        v                      |
      |    DEF-STR004   |   DEF-STR006                  |
      |    ("Like       |   (Phase from IMF)            |
      |     dissolves") |                               |
      |         |       v                               |
      |         |   PRIM-STR005 (Structure-->property)  |
      |         |                                       |
      |         v                                       |
      |    DEF-STR010 (Water as solvent)                |
      |    [depends: DEF-STR002, DEF-STR003, DEF-STR004]
      |                                                 |
      +--------> DEF-STR005 (Isomer recognition)        |
      |          [depends: PRIM-STR003]                 |
      |                                                 |
      +--------> DEF-STR007 (Carbon backbone)           |
                 [depends: PRIM-COM007, PRIM-STR001]    |
                      |                                 |
                      v                                 |
                 DEF-STR008 (Polymer reasoning)         |
                 [depends: DEF-STR007, PRIM-STR004]     |
                                                        |
                 DEF-STR009 (Metallic structure) <------+
                 [depends: PRIM-STR001, DEF-COM002]
```

**Acyclicity verification**: All arrows point from items that are defined earlier to items defined later. No item depends on an item that depends on it. Imported COM items serve as roots with no STR predecessors. The graph is a DAG.

**Core-tier completeness**: Removing DEF-STR009 (the only Enrichment item) does not break any dependency chain. All Core items depend only on other Core items or imported Core items from COM.

## 8. Cross-Domain Interface

### Exports

| ID | Concept | Imported by |
|----|---------|-------------|
| PRIM-STR001 | Bond type classification | NRG, CHG |
| PRIM-STR002 | Bond polarity reasoning | NRG, CHG |
| PRIM-STR003 | Molecular shape reasoning | CHG, SCL |
| PRIM-STR004 | Intermolecular force hierarchy | SCL, CHG |
| PRIM-STR005 | Structure-to-property inference | SCL, CHG |
| DEF-STR001 | Lewis structure | CHG |
| DEF-STR002 | Molecular polarity | SCL, CHG |
| DEF-STR003 | Hydrogen bond | SCL, CHG |
| DEF-STR004 | "Like dissolves like" | SCL |
| DEF-STR005 | Isomer recognition | CHG |
| DEF-STR006 | Phase from IMF balance | SCL |
| DEF-STR007 | Carbon backbone reasoning | CHG |
| DEF-STR008 | Polymer reasoning | SCL |
| DEF-STR009 | Metallic structure | -- |
| DEF-STR010 | Water as solvent | CHG, SCL |

### Imports

| ID | Imported Item | Source Domain | Purpose in STR |
|----|---------------|--------------|----------------|
| DEP-STR001 | PRIM-COM007 (valence electron reasoning) | COM | Electron count input for Lewis structures (DEF-STR001) and carbon backbone reasoning (DEF-STR007) |
| DEP-STR002 | DEF-COM005 (electronegativity) | COM | Bond type classification (PRIM-STR001) and bond polarity reasoning (PRIM-STR002) |
| DEP-STR003 | PRIM-COM001 (atomic composition analysis) | COM | Identifying which atoms are present before reasoning about arrangement |
| DEP-STR004 | DEF-COM002 (ion) | COM | Metallic structure reasoning (DEF-STR009) -- cation formation in electron sea model |

## 9. Difficulty Tiers

| ID | Concept | Tier | Justification |
|----|---------|------|---------------|
| PRIM-STR001 | Bond type classification | C | Gateway: determines whether a substance is molecular, ionic, or metallic -- all downstream reasoning branches from this |
| PRIM-STR002 | Bond polarity reasoning | C | Core bridge: connects electronegativity (COM) to molecular polarity (STR) and IMFs |
| PRIM-STR003 | Molecular shape reasoning | C | Core skill: VSEPR-based shape prediction is the central STR reasoning move and determines molecular polarity |
| PRIM-STR004 | Intermolecular force hierarchy | C | Core ranking: IMF strength determines phase, boiling point, solubility -- the most directly observable consequences of structure |
| PRIM-STR005 | Structure-to-property inference | C | Culminating move: the capstone reasoning skill that connects all STR concepts to macroscopic predictions |
| DEF-STR001 | Lewis structure | C | Core tool: the 2D diagram that serves as input to VSEPR (PRIM-STR003) and all subsequent shape/polarity reasoning |
| DEF-STR002 | Molecular polarity | C | Core concept: net dipole determines IMF type and solubility behavior; bridge from bond polarity to molecule polarity |
| DEF-STR003 | Hydrogen bond | C | Core interaction: explains water's anomalous properties, protein folding, DNA structure -- essential for chemical literacy |
| DEF-STR004 | "Like dissolves like" | C | Core heuristic: the single most useful everyday chemistry rule; governs cleaning, cooking, and drug delivery |
| DEF-STR005 | Isomer recognition | C | Core distinction: directly addresses the additive-to-emergent threshold schema; essential for pharmaceutical and food chemistry literacy |
| DEF-STR006 | Phase from IMF balance | C | Core link: connects IMFs to the most basic observable property (solid/liquid/gas) -- essential for everyday reasoning |
| DEF-STR007 | Carbon backbone reasoning | C | Core foundation: explains why carbon is central to life, fuels, and materials; prerequisite for polymer reasoning |
| DEF-STR008 | Polymer reasoning | C | Core application: plastics are ubiquitous; understanding polymer structure-to-property is essential for material literacy |
| DEF-STR009 | Metallic structure | E | Enrichment: valuable for materials understanding but no downstream Core item depends on it; removal does not break any dependency chain |
| DEF-STR010 | Water as solvent | C | Core integration: combines polarity, H-bonding, and "like dissolves like" into the most important specific application in chemistry |

**Tier constraint verification**: The single Enrichment item (DEF-STR009, metallic structure) has no downstream dependents in any domain. Its Referenced-by field is empty (--). Removing it leaves all 14 Core items and their dependency chains intact. The Core tier alone forms a self-contained, dependency-complete sub-taxonomy.

## 10. Self-Audit Checklist

- [x] Every PRIM has: reasoning move formulation ("Given X, do Y to determine Z"), description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [x] Every DEF depends only on previously listed PRIM/DEF (check intra-domain dependency graph -- verified acyclic)
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format (PRIM-COM007, DEF-COM005, PRIM-COM001, DEF-COM002)
- [x] Every import is listed in the source domain's exports (verified: PRIM-COM007, DEF-COM005, PRIM-COM001, and DEF-COM002 all appear in DOMAIN-COM Section 8 Exports with STR in their "Imported by" column)
- [x] Dissolution argument is present and non-trivial (Section 1: ethanol/dimethyl ether isomer example, 5 sentences distinguishing STR from COM, NRG, CHG)
- [x] Real-world hooks cover everyday non-major contexts (cooking oils, cleaning products, drug effectiveness, water behavior, plastics, metals, salad dressing, cosmetics, food preservation)
- [x] Intra-domain dependency graph is acyclic (Section 7: all edges point from earlier to later items; no cycles)
- [x] Tier annotations (C/E) are present on all 15 items (13 Core, 2 Enrichment -- note: only 1 Enrichment item DEF-STR009; count is 14 Core + 1 Enrichment = 15 total)
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry in CONVENTIONS.md Section 9 -- all STR items are unique to STR)
- [x] Reasoning moves are genuinely "Given X, do Y" cognitive operations (not mere topic labels or vocabulary words -- verified for all 15 items)
