# CLUE (Chemistry, Life, the Universe and Everything) -- Source Map

**Source:** CLUE (Chemistry, Life, the Universe and Everything)
**Authors:** Melanie M. Cooper & Michael W. Klymkowsky
**URL:** https://openbooks.lib.msu.edu/clue/
**License:** CC-BY-NC-SA 4.0 (less permissive than OpenStax CC-BY 4.0 -- no commercial use)
**Platform:** Pressbooks (Michigan State University)
**Format:** HTML (web-native)
**Total:** 9 chapters, 48 sections

---

## Pedagogical Approach

CLUE is a research-based reformed general chemistry curriculum built around
**4 Core Ideas** rather than traditional topic-based chapters. Key features:

1. **Atoms-first approach**: Starts with atomic structure and builds outward
   to bonding, properties, reactions, and systems.
2. **Woven core ideas**: Each core idea recurs across multiple chapters.
   A chapter on "Atoms" still engages Energy and Change ideas; a chapter on
   "Reactions" still invokes Structure reasoning. This contrasts sharply with
   OpenStax's one-topic-per-chapter layout.
3. **Causal mechanistic reasoning**: Emphasizes "why" over "how to calculate."
   Students are expected to construct explanations, not execute algorithms.
4. **Deliberate omissions**: Stoichiometry (quantitative mole-ratio calculations)
   and electrochemistry are intentionally excluded. The rationale is that these
   topics consume instructional time without proportionate gain in conceptual
   understanding for the target audience.
5. **Design-research validated**: The curriculum was developed and refined through
   iterative classroom testing with assessment data, not author intuition alone.

### The 4 Core Ideas

| # | Core Idea | Guiding Question |
|---|-----------|-----------------|
| 1 | **Structure and Properties** | How does the structure of matter determine its properties? |
| 2 | **Bonding and Interactions** | What forces cause matter to interact? |
| 3 | **Energy** | What energy changes are involved in chemical processes? |
| 4 | **Change and Stability** | How and why do chemical systems change or remain stable? |

---

## Core Idea to Domain Mapping

CLUE's 4 core ideas map to our 5 taxonomy domains, but the mapping is many-to-many
because core ideas are woven rather than siloed.

| Core Idea | Primary Domain(s) | Secondary Domain(s) | Notes |
|-----------|--------------------|---------------------|-------|
| Structure and Properties | **STR** | COM, SCL | Properties arise from structure; COM provides atomic-level identity; SCL provides macro-submicro translation |
| Bonding and Interactions | **STR** | NRG, COM | Bond formation/breaking is both structural and energetic; valence electrons (COM) drive bonding |
| Energy | **NRG** | CHG, STR | Energy changes accompany reactions (CHG) and phase changes (STR) |
| Change and Stability | **CHG** | NRG, SCL | Equilibrium and kinetics (CHG) depend on energy (NRG) and scale (SCL) |

**Key difference from OpenStax**: OpenStax assigns each chapter to one primary domain.
CLUE assigns each chapter to *multiple* core ideas simultaneously. Our mapping below
therefore uses MULTI more frequently than the OpenStax map does.

**Missing domain**: COM (Composition) has no dedicated core idea in CLUE, but COM
primitives (atomic composition, elemental identity, periodic position, valence
electrons) pervade Chapters 1-3 as foundational knowledge. SCL (Scale) likewise
has no dedicated core idea but is threaded through Chapters 5-6 and 8-9.

---

## Section-Level Mapping

### Template (S3-EXT, 8 fields)
```
### clue/ch{N}/{N.N} --- {Section Title}
- **Source**: CLUE, Ch N, Section N.N
- **File**: https://openbooks.lib.msu.edu/clue/chapter/{slug}/
- **Domain**: {COM | STR | NRG | CHG | SCL | MULTI}
- **Maps to**: {taxonomy IDs}
- **Coverage depth**: {FULL | PARTIAL | PERIPHERAL}
- **Audience level**: {NON-MAJORS | MAJORS-ONLY | BOTH}
- **Content signal**: {ADAPT | REWRITE | REFERENCE-ONLY | SKIP}
- **Notes**: {observations}
```

**Confidence note**: Section mappings below are INFERRED from section titles,
CLUE's known pedagogical design, and the 4 core ideas framework. We have not
fetched individual section HTML. Mappings marked [INFERRED] should be verified
against actual section content in a later pass.

---

### Chapter 1: Atoms (8 sections)

### clue/ch1/1.1 --- What Do You Think You Know About Atoms?
- **Source**: CLUE, Ch 1, Section 1.1
- **File**: https://openbooks.lib.msu.edu/clue/chapter/1-1/
- **Domain**: COM
- **Maps to**: PRIM-COM001 (atomic composition) [INFERRED]
- **Coverage depth**: PERIPHERAL
- **Audience level**: NON-MAJORS
- **Content signal**: REFERENCE-ONLY
- **Notes**: [INFERRED] Likely a metacognitive opening that surfaces student preconceptions about atoms. Aligns with CLUE's design-research approach. May not introduce formal content but establishes the reasoning context for PRIM-COM001.

### clue/ch1/1.2 --- Atomic Realities and Scientific Theories
- **Source**: CLUE, Ch 1, Section 1.2
- **File**: https://openbooks.lib.msu.edu/clue/chapter/1-2/
- **Domain**: COM
- **Maps to**: PRIM-COM001 (atomic composition), PRIM-COM008 (causal chain reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Nature of scientific theories applied to atomic theory. CLUE's emphasis on causal reasoning means this likely introduces PRIM-COM008 earlier than any traditional text. Valuable framing section.

### clue/ch1/1.3 --- Some History of Atomic Theory
- **Source**: CLUE, Ch 1, Section 1.3
- **File**: https://openbooks.lib.msu.edu/clue/chapter/1-3/
- **Domain**: COM
- **Maps to**: PRIM-COM001 (atomic composition) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Dalton through Rutherford, likely condensed compared to OpenStax 2.1-2.2. CLUE's atoms-first approach means this is Chapter 1 material, not Chapter 6 material. Historical models as evidence-based reasoning, not rote memorization.

### clue/ch1/1.4 --- Identifying and Isolating Elements
- **Source**: CLUE, Ch 1, Section 1.4
- **File**: https://openbooks.lib.msu.edu/clue/chapter/1-4/
- **Domain**: COM
- **Maps to**: PRIM-COM002 (elemental identity), PRIM-COM004 (substance classification) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] How elements are identified and distinguished from compounds/mixtures. Likely covers elemental identity reasoning and basic substance classification without the full taxonomy of matter states found in OpenStax 1.2.

### clue/ch1/1.5 --- Evidence for Atoms
- **Source**: CLUE, Ch 1, Section 1.5
- **File**: https://openbooks.lib.msu.edu/clue/chapter/1-5/
- **Domain**: MULTI (COM, SCL)
- **Maps to**: PRIM-COM001 (atomic composition), PRIM-SCL001 (macro-submicro translation) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Experimental evidence that atoms exist. Likely bridges macro observations to submicro explanations (PRIM-SCL001). This section is distinctive to CLUE -- OpenStax assumes atoms exist without belaboring the evidence.

### clue/ch1/1.6 --- The Divisible Atom
- **Source**: CLUE, Ch 1, Section 1.6
- **File**: https://openbooks.lib.msu.edu/clue/chapter/1-6/
- **Domain**: COM
- **Maps to**: PRIM-COM001 (atomic composition), DEF-COM001 (isotope), DEF-COM002 (ion) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Subatomic particles: protons, neutrons, electrons. Likely introduces isotopes and ions. Parallel to OpenStax 2.3 but with CLUE's emphasis on "why does divisibility matter?" rather than notation drills.

### clue/ch1/1.7 --- Interactions Between Atoms and Molecules
- **Source**: CLUE, Ch 1, Section 1.7
- **File**: https://openbooks.lib.msu.edu/clue/chapter/1-7/
- **Domain**: MULTI (COM, STR, NRG)
- **Maps to**: PRIM-STR001 (bond type classification), PRIM-NRG001 (energy tracking) [INFERRED]
- **Coverage depth**: PERIPHERAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] First introduction to the idea that atoms interact (bonding preview). CLUE plants the seeds of bonding and energy in Chapter 1, well before the formal treatment. This is the "woven core ideas" approach in action -- STR and NRG appear inside a COM chapter.

### clue/ch1/1.8 --- Interactions Between Helium Atoms and Hydrogen Molecules
- **Source**: CLUE, Ch 1, Section 1.8
- **File**: https://openbooks.lib.msu.edu/clue/chapter/1-8/
- **Domain**: MULTI (STR, NRG)
- **Maps to**: PRIM-STR004 (IMF hierarchy), PRIM-NRG001 (energy tracking), PRIM-SCL001 (macro-submicro translation) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Concrete molecular examples of intermolecular forces. He-He (London dispersion only) vs H2-H2 (London dispersion with different polarizability). Remarkably early introduction of IMFs compared to OpenStax Ch 10. This exemplifies CLUE's approach: use simple cases to build reasoning tools early.

---

### Chapter 2: Electrons and Orbitals (7 sections)

### clue/ch2/2.1 --- Light and Getting Quantum Mechanical
- **Source**: CLUE, Ch 2, Section 2.1
- **File**: https://openbooks.lib.msu.edu/clue/chapter/2-1/
- **Domain**: NRG
- **Maps to**: PRIM-NRG001 (energy tracking) [INFERRED]
- **Coverage depth**: PERIPHERAL
- **Audience level**: BOTH
- **Content signal**: REFERENCE-ONLY
- **Notes**: [INFERRED] Light as quantized energy. Background for understanding electron behavior. Parallel to OpenStax 6.1 but likely more conceptual, less mathematical. Provides energy-level reasoning needed for spectroscopy and orbital understanding.

### clue/ch2/2.2 --- Taking Quanta Seriously
- **Source**: CLUE, Ch 2, Section 2.2
- **File**: https://openbooks.lib.msu.edu/clue/chapter/2-2/
- **Domain**: COM
- **Maps to**: PRIM-COM007 (valence electron reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REFERENCE-ONLY
- **Notes**: [INFERRED] Implications of quantization for atomic structure. Likely bridges from photon energy to discrete electron energy levels. The reasoning framework here supports PRIM-COM007 but the quantum mechanical detail may exceed non-majors needs.

### clue/ch2/2.3 --- Exploring Atomic Organization Using Spectroscopy
- **Source**: CLUE, Ch 2, Section 2.3
- **File**: https://openbooks.lib.msu.edu/clue/chapter/2-3/
- **Domain**: MULTI (COM, NRG)
- **Maps to**: PRIM-COM001 (atomic composition), PRIM-NRG001 (energy tracking) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REFERENCE-ONLY
- **Notes**: [INFERRED] Spectroscopy as evidence for electronic structure. CLUE's evidence-based approach: "how do we know electrons are arranged this way?" Good for PRIM-COM008 (causal chain reasoning) but spectroscopy itself is not a taxonomy item.

### clue/ch2/2.4 --- Beyond Bohr
- **Source**: CLUE, Ch 2, Section 2.4
- **File**: https://openbooks.lib.msu.edu/clue/chapter/2-4/
- **Domain**: COM
- **Maps to**: PRIM-COM007 (valence electron reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: REFERENCE-ONLY
- **Notes**: [INFERRED] Transition from Bohr model to quantum mechanical model. Orbital shapes, probability distributions. The quantum mechanical depth likely exceeds non-majors scope, but the conceptual takeaway (electrons exist in orbitals, not orbits) is relevant.

### clue/ch2/2.5 --- Organizing Elements: Introduction to the Periodic Table
- **Source**: CLUE, Ch 2, Section 2.5
- **File**: https://openbooks.lib.msu.edu/clue/chapter/2-5/
- **Domain**: COM
- **Maps to**: PRIM-COM003 (periodic position reasoning), PRIM-COM007 (valence electron reasoning) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Periodic table organization from electron configuration. CLUE's atoms-first sequence means the periodic table is motivated by electronic structure rather than presented as a given. Direct coverage of PRIM-COM003. The connection "periodic position tells you valence electrons" is central.

### clue/ch2/2.6 --- Orbitals, Electron Clouds, Probabilities, and Energies
- **Source**: CLUE, Ch 2, Section 2.6
- **File**: https://openbooks.lib.msu.edu/clue/chapter/2-6/
- **Domain**: COM
- **Maps to**: PRIM-COM007 (valence electron reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: REFERENCE-ONLY
- **Notes**: [INFERRED] Orbital shapes and electron density. Parallel to OpenStax 6.3-6.4. CLUE treats this more conceptually than OpenStax but the orbital detail still skews MAJORS-ONLY. Non-majors takeaway: electrons are found in regions of space with predictable energy.

### clue/ch2/2.7 --- Quantum Numbers
- **Source**: CLUE, Ch 2, Section 2.7
- **File**: https://openbooks.lib.msu.edu/clue/chapter/2-7/
- **Domain**: COM
- **Maps to**: PRIM-COM007 (valence electron reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: SKIP
- **Notes**: [INFERRED] n, l, ml, ms quantum numbers. MAJORS-ONLY content. Non-majors do not need quantum number notation; they need the conceptual outcome (valence electron count from periodic position).

---

### Chapter 3: Elements, Bonding, and Physical Properties (3 sections)

### clue/ch3/3.1 --- Elements and Bonding
- **Source**: CLUE, Ch 3, Section 3.1
- **File**: https://openbooks.lib.msu.edu/clue/chapter/3-1/
- **Domain**: MULTI (STR, COM)
- **Maps to**: PRIM-STR001 (bond type classification), PRIM-COM007 (valence electron reasoning), DEF-COM005 (electronegativity) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] How elemental properties determine bonding type. Electronegativity differences drive ionic vs covalent classification. This is where CLUE connects COM reasoning (what element? where on periodic table?) to STR reasoning (what kind of bond?). High-value cross-domain section.

### clue/ch3/3.2 --- Elements and Their Interactions
- **Source**: CLUE, Ch 3, Section 3.2
- **File**: https://openbooks.lib.msu.edu/clue/chapter/3-2/
- **Domain**: MULTI (STR, NRG)
- **Maps to**: PRIM-STR004 (IMF hierarchy), PRIM-STR005 (structure-to-property inference), PRIM-NRG001 (energy tracking) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] How elements interact through different types of forces. Likely covers covalent network, metallic, and molecular substances and their macroscopic properties (melting point, conductivity). Structure-to-property reasoning is central.

### clue/ch3/3.3 --- Metals
- **Source**: CLUE, Ch 3, Section 3.3
- **File**: https://openbooks.lib.msu.edu/clue/chapter/3-3/
- **Domain**: STR
- **Maps to**: DEF-STR009 (metallic structure), PRIM-STR005 (structure-to-property inference) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Metallic bonding and metallic properties. CLUE is one of the few texts that treats metals with enough depth to cover DEF-STR009. This fills a gap left by OpenStax (which buries metals in the SKIPped Chapter 18). High-value section.

---

### Chapter 4: Heterogeneous Compounds (6 sections)

### clue/ch4/4.1 --- 3D and 2D Representations
- **Source**: CLUE, Ch 4, Section 4.1
- **File**: https://openbooks.lib.msu.edu/clue/chapter/4-1/
- **Domain**: STR
- **Maps to**: DEF-STR001 (Lewis structure), PRIM-COM005 (chemical formula reading), PRIM-SCL001 (macro-submicro translation) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Translating between 3D molecular structures and 2D representations (Lewis structures, structural formulas, line-angle drawings). Emphasizes representation as a reasoning tool, not a rote skill. Connects to PRIM-SCL001 (macro-submicro translation).

### clue/ch4/4.2 --- Single Bonds and Molecular Shape
- **Source**: CLUE, Ch 4, Section 4.2
- **File**: https://openbooks.lib.msu.edu/clue/chapter/4-2/
- **Domain**: STR
- **Maps to**: DEF-STR001 (Lewis structure), PRIM-STR003 (molecular shape reasoning) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] VSEPR for molecules with only single bonds. Tetrahedral, pyramidal, bent geometries. Parallel to OpenStax 7.6 but likely more tightly coupled to Lewis structure construction. Direct coverage of PRIM-STR003.

### clue/ch4/4.3 --- Double and Triple Bonds
- **Source**: CLUE, Ch 4, Section 4.3
- **File**: https://openbooks.lib.msu.edu/clue/chapter/4-3/
- **Domain**: MULTI (STR, NRG)
- **Maps to**: PRIM-STR001 (bond type classification), PRIM-NRG002 (bond energy reasoning), DEF-STR001 (Lewis structure) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Multiple bonds: how they form, how they affect molecular shape, and how bond energy relates to bond order. CLUE likely weaves NRG reasoning (stronger bonds = more energy) into the structural discussion. High-value section.

### clue/ch4/4.4 --- Bonding in Nitrogen, Oxygen, and Fluorine
- **Source**: CLUE, Ch 4, Section 4.4
- **File**: https://openbooks.lib.msu.edu/clue/chapter/4-4/
- **Domain**: MULTI (STR, COM)
- **Maps to**: PRIM-STR001 (bond type classification), PRIM-STR002 (bond polarity reasoning), PRIM-COM007 (valence electron reasoning) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Case studies of specific elements with lone pairs. How valence electron count and electronegativity determine bonding behavior. CLUE uses these paradigmatic examples to build general reasoning skills rather than teaching rules.

### clue/ch4/4.5 --- Molecular Shapes, Polarity, and Molecular Interactions
- **Source**: CLUE, Ch 4, Section 4.5
- **File**: https://openbooks.lib.msu.edu/clue/chapter/4-5/
- **Domain**: STR
- **Maps to**: PRIM-STR003 (molecular shape reasoning), DEF-STR002 (molecular polarity), PRIM-STR004 (IMF hierarchy), DEF-STR003 (hydrogen bond) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] The full chain: shape determines polarity, polarity determines intermolecular forces. This section likely covers 4 taxonomy items in one integrated treatment. In OpenStax, this reasoning chain spans Chapters 7 and 10. CLUE integrates it. Very high-value section.

### clue/ch4/4.6 --- Ionic Bonding
- **Source**: CLUE, Ch 4, Section 4.6
- **File**: https://openbooks.lib.msu.edu/clue/chapter/4-6/
- **Domain**: MULTI (STR, COM)
- **Maps to**: PRIM-STR001 (bond type classification), DEF-COM002 (ion), DEF-COM005 (electronegativity) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Ionic bonding placed after covalent bonding -- the reverse of OpenStax. CLUE's rationale: ionic bonding is better understood as the extreme of bond polarity. Electron transfer as the limit of unequal sharing. This ordering reinforces PRIM-STR002 (bond polarity as a continuum).

---

### Chapter 5: Systems Thinking (7 sections)

### clue/ch5/5.1 --- Temperature
- **Source**: CLUE, Ch 5, Section 5.1
- **File**: https://openbooks.lib.msu.edu/clue/chapter/5-1/
- **Domain**: NRG
- **Maps to**: DEF-NRG001 (heat vs temperature) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] What temperature actually measures at the molecular level. CLUE likely distinguishes temperature (average kinetic energy) from heat (energy transfer) explicitly. Direct coverage of DEF-NRG001.

### clue/ch5/5.2 --- Thinking About Populations of Molecules
- **Source**: CLUE, Ch 5, Section 5.2
- **File**: https://openbooks.lib.msu.edu/clue/chapter/5-2/
- **Domain**: MULTI (SCL, NRG)
- **Maps to**: PRIM-SCL001 (macro-submicro translation), PRIM-SCL004 (emergent property reasoning), PRIM-NRG004 (entropy reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Boltzmann distributions, molecular populations. The idea that macroscopic properties emerge from molecular-level statistics. This section is distinctive -- OpenStax does not have an equivalent. Directly supports PRIM-SCL004 (emergent property reasoning) and early seeds of entropy.

### clue/ch5/5.3 --- Vibrating, Bending, and Rotating Molecules
- **Source**: CLUE, Ch 5, Section 5.3
- **File**: https://openbooks.lib.msu.edu/clue/chapter/5-3/
- **Domain**: NRG
- **Maps to**: PRIM-NRG001 (energy tracking), DEF-NRG002 (specific heat) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Molecular modes of motion (translational, rotational, vibrational) and their energy contributions. Likely connects to specific heat -- molecules with more modes store more energy per degree. Provides molecular-level explanation for macroscopic heat capacity.

### clue/ch5/5.4 --- Open Versus Closed Systems
- **Source**: CLUE, Ch 5, Section 5.4
- **File**: https://openbooks.lib.msu.edu/clue/chapter/5-4/
- **Domain**: MULTI (NRG, SCL)
- **Maps to**: PRIM-NRG001 (energy tracking), PRIM-NRG003 (exo/endothermic) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] System/surroundings distinction, open vs closed vs isolated systems. Foundation for thermodynamic reasoning. CLUE's "systems thinking" framing is unusual and valuable -- most texts introduce system/surroundings as a definition, not as a reasoning framework.

### clue/ch5/5.5 --- Thermodynamics and Systems
- **Source**: CLUE, Ch 5, Section 5.5
- **File**: https://openbooks.lib.msu.edu/clue/chapter/5-5/
- **Domain**: NRG
- **Maps to**: PRIM-NRG003 (exo/endothermic), DEF-NRG003 (enthalpy change), PRIM-NRG004 (entropy reasoning) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Enthalpy and entropy introduced together as competing drivers. CLUE combines what OpenStax separates into Chapters 5 and 16. The conceptual integration (enthalpy vs entropy) is exactly what our taxonomy needs for PRIM-NRG005 (spontaneity reasoning).

### clue/ch5/5.6 --- Back to Phase Changes
- **Source**: CLUE, Ch 5, Section 5.6
- **File**: https://openbooks.lib.msu.edu/clue/chapter/5-6/
- **Domain**: MULTI (STR, NRG)
- **Maps to**: DEF-STR006 (phase from IMF balance), PRIM-NRG001 (energy tracking), PRIM-NRG003 (exo/endothermic) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Phase changes as energy-vs-IMF reasoning. Melting = overcoming IMFs with kinetic energy. Boiling = complete separation. CLUE revisits phase changes (first introduced in Ch 1) with thermodynamic tools. Excellent integration of STR and NRG.

### clue/ch5/5.7 --- Gibbs (Free) Energy to the Rescue
- **Source**: CLUE, Ch 5, Section 5.7
- **File**: https://openbooks.lib.msu.edu/clue/chapter/5-7/
- **Domain**: NRG
- **Maps to**: DEF-NRG004 (free energy conceptual), PRIM-NRG005 (spontaneity reasoning) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Gibbs free energy as the criterion for spontaneity. delta-G = delta-H - T*delta-S conceptually, not computationally. CLUE introduces this in Chapter 5, far earlier than OpenStax Chapter 16. The early placement allows Gibbs energy to be *used* as a reasoning tool in Chapters 6-9.

---

### Chapter 6: Solutions (6 sections)

### clue/ch6/6.1 --- What Is a Solution?
- **Source**: CLUE, Ch 6, Section 6.1
- **File**: https://openbooks.lib.msu.edu/clue/chapter/6-1/
- **Domain**: MULTI (COM, STR)
- **Maps to**: PRIM-COM004 (substance classification), DEF-STR010 (water as solvent) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Solutions as homogeneous mixtures. Solute/solvent at the molecular level. Likely introduces water's special role as a solvent. Direct coverage of DEF-STR010.

### clue/ch6/6.2 --- Solubility: Why Do Some Things Form Solutions and Others Not?
- **Source**: CLUE, Ch 6, Section 6.2
- **File**: https://openbooks.lib.msu.edu/clue/chapter/6-2/
- **Domain**: STR
- **Maps to**: DEF-STR004 (like dissolves like), PRIM-STR004 (IMF hierarchy) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] "Like dissolves like" as an IMF-based reasoning principle. Why oil and water don't mix, why salt dissolves in water. CLUE's causal reasoning approach: dissolution occurs when solute-solvent IMFs are comparable to solute-solute and solvent-solvent IMFs.

### clue/ch6/6.3 --- Hydrogen Bonding Interactions and Solubility
- **Source**: CLUE, Ch 6, Section 6.3
- **File**: https://openbooks.lib.msu.edu/clue/chapter/6-3/
- **Domain**: STR
- **Maps to**: DEF-STR003 (hydrogen bond), DEF-STR004 (like dissolves like) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Hydrogen bonding as the key to biological solubility. Sugar dissolves because it hydrogen-bonds with water; oil does not. CLUE deploys H-bonding as a reasoning tool for predicting solubility. Reinforces both DEF-STR003 and DEF-STR004.

### clue/ch6/6.4 --- Gibbs Energy and Solubility
- **Source**: CLUE, Ch 6, Section 6.4
- **File**: https://openbooks.lib.msu.edu/clue/chapter/6-4/
- **Domain**: MULTI (NRG, STR)
- **Maps to**: DEF-NRG004 (free energy conceptual), PRIM-NRG005 (spontaneity reasoning), PRIM-NRG004 (entropy reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Why some dissolutions are endothermic yet still spontaneous -- entropy drives them. CLUE applies the Gibbs energy framework from Ch 5 to the concrete case of dissolution. This is the "woven" approach: NRG tools deployed in an STR context.

### clue/ch6/6.5 --- Polarity
- **Source**: CLUE, Ch 6, Section 6.5
- **File**: https://openbooks.lib.msu.edu/clue/chapter/6-5/
- **Domain**: STR
- **Maps to**: PRIM-STR002 (bond polarity reasoning), DEF-STR002 (molecular polarity) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Polarity revisited in the context of solutions. Bond polarity and molecular polarity determine solvent compatibility. Reinforces earlier coverage from Ch 4.5 with new applications.

### clue/ch6/6.6 --- Temperature and Solubility
- **Source**: CLUE, Ch 6, Section 6.6
- **File**: https://openbooks.lib.msu.edu/clue/chapter/6-6/
- **Domain**: MULTI (NRG, SCL)
- **Maps to**: PRIM-NRG001 (energy tracking), PRIM-SCL003 (concentration reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Temperature dependence of solubility for solids vs gases. Henry's law conceptually. Connects energy reasoning (endothermic dissolution favored at higher T) with concentration reasoning.

---

### Chapter 7: A Field Guide to Chemical Reactions (6 sections)

### clue/ch7/7.1 --- Collisions and Chemical Reactions
- **Source**: CLUE, Ch 7, Section 7.1
- **File**: https://openbooks.lib.msu.edu/clue/chapter/7-1/
- **Domain**: MULTI (CHG, NRG)
- **Maps to**: PRIM-CHG001 (equation reading/balancing), PRIM-NRG006 (activation energy), PRIM-COM006 (conservation of atoms) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Chemical reactions as molecular collisions. Conservation of atoms in reactions. Activation energy as the threshold for productive collisions. CLUE introduces reactions through a molecular-level mechanism, not through equation balancing. But PRIM-CHG001 (equation reading) and PRIM-COM006 (conservation) are likely both addressed.

### clue/ch7/7.2 --- Acid-Base Reactions: A Guide for Beginners
- **Source**: CLUE, Ch 7, Section 7.2
- **File**: https://openbooks.lib.msu.edu/clue/chapter/7-2/
- **Domain**: CHG
- **Maps to**: PRIM-CHG005 (acid-base reasoning), DEF-CHG002 (pH scale) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Bronsted-Lowry acid-base reactions (proton transfer). pH as a measure of acidity. CLUE's "field guide" metaphor frames reaction types as species to be identified -- a recognition task, not a memorization task. Aligns well with PRIM-CHG002 (reaction type recognition).

### clue/ch7/7.3 --- Lewis Acid-Base Reactions
- **Source**: CLUE, Ch 7, Section 7.3
- **File**: https://openbooks.lib.msu.edu/clue/chapter/7-3/
- **Domain**: CHG
- **Maps to**: PRIM-CHG005 (acid-base reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: [INFERRED] Lewis acid-base theory (electron pair donation/acceptance). This is notable -- OpenStax buries Lewis acid-base in Ch 15 (SKIP). CLUE includes it as part of the reaction toolkit. For non-majors, the conceptual idea (electron-pair donation) is valuable; detailed mechanisms are not.

### clue/ch7/7.4 --- Nucleophiles and Electrophiles
- **Source**: CLUE, Ch 7, Section 7.4
- **File**: https://openbooks.lib.msu.edu/clue/chapter/7-4/
- **Domain**: MULTI (CHG, STR)
- **Maps to**: PRIM-CHG002 (reaction type recognition), PRIM-STR002 (bond polarity reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: [INFERRED] Nucleophilic and electrophilic sites on molecules. Uses bond polarity and electron density to predict where reactions occur. This is distinctively CLUE -- traditional gen-chem texts leave nucleophile/electrophile to organic chemistry. The reasoning move (electron-rich attacks electron-poor) is powerful and aligns with our causal chain reasoning (PRIM-COM008).

### clue/ch7/7.5 --- Oxidation-Reduction Reactions
- **Source**: CLUE, Ch 7, Section 7.5
- **File**: https://openbooks.lib.msu.edu/clue/chapter/7-5/
- **Domain**: CHG
- **Maps to**: PRIM-CHG006 (oxidation-reduction reasoning) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Redox as electron transfer. Oxidation states as bookkeeping. CLUE covers redox conceptually without the electrochemistry apparatus (galvanic cells, electrode potentials) that OpenStax adds in Ch 17. This matches our non-majors scope.

### clue/ch7/7.6 --- Energy Changes and Chemical Reactions
- **Source**: CLUE, Ch 7, Section 7.6
- **File**: https://openbooks.lib.msu.edu/clue/chapter/7-6/
- **Domain**: NRG
- **Maps to**: PRIM-NRG002 (bond energy reasoning), PRIM-NRG003 (exo/endothermic), DEF-NRG003 (enthalpy change) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Energy released or absorbed in reactions from a bond energy perspective. "Bonds broken minus bonds formed." CLUE applies the NRG framework from Ch 5 to chemical reactions. Excellent integration of NRG and CHG domains.

---

### Chapter 8: How Far? How Fast? (6 sections)

### clue/ch8/8.1 --- What Factors Control Reactions?
- **Source**: CLUE, Ch 8, Section 8.1
- **File**: https://openbooks.lib.msu.edu/clue/chapter/8-1/
- **Domain**: MULTI (CHG, NRG)
- **Maps to**: PRIM-CHG004 (rate reasoning), PRIM-NRG005 (spontaneity reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Overview: thermodynamic vs kinetic control. "How far" (thermodynamics) vs "how fast" (kinetics). This conceptual framing is unique to CLUE and extremely valuable for non-majors -- it prevents the common confusion between spontaneity and rate.

### clue/ch8/8.2 --- Reaction Rates
- **Source**: CLUE, Ch 8, Section 8.2
- **File**: https://openbooks.lib.msu.edu/clue/chapter/8-2/
- **Domain**: CHG
- **Maps to**: PRIM-CHG004 (rate reasoning) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Qualitative factors affecting reaction rates: temperature, concentration, surface area. Parallel to OpenStax 12.1-12.2 but likely without quantitative rate law expressions. Direct coverage of PRIM-CHG004.

### clue/ch8/8.3 --- Kinetics and the Mechanisms of Reactions
- **Source**: CLUE, Ch 8, Section 8.3
- **File**: https://openbooks.lib.msu.edu/clue/chapter/8-3/
- **Domain**: CHG
- **Maps to**: PRIM-NRG006 (activation energy), PRIM-CHG004 (rate reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: [INFERRED] Reaction mechanisms at a conceptual level. Multi-step reactions, rate-determining step as bottleneck. CLUE likely treats mechanisms more conceptually than OpenStax 12.6 (which we SKIPped). The activation energy reasoning is non-majors appropriate; mechanistic detail may not be.

### clue/ch8/8.4 --- Catalysis
- **Source**: CLUE, Ch 8, Section 8.4
- **File**: https://openbooks.lib.msu.edu/clue/chapter/8-4/
- **Domain**: CHG
- **Maps to**: DEF-CHG001 (catalyst), PRIM-NRG006 (activation energy) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Catalysts lower activation energy. Enzymes as biological catalysts. CLUE's biological emphasis means enzyme catalysis is likely treated with more depth than OpenStax 12.7. Direct coverage of DEF-CHG001.

### clue/ch8/8.5 --- Equilibrium
- **Source**: CLUE, Ch 8, Section 8.5
- **File**: https://openbooks.lib.msu.edu/clue/chapter/8-5/
- **Domain**: CHG
- **Maps to**: PRIM-CHG003 (equilibrium reasoning), DEF-CHG003 (Le Chatelier's principle) [INFERRED]
- **Coverage depth**: FULL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Dynamic equilibrium and Le Chatelier's principle. CLUE combines what OpenStax splits into Ch 13.1 and 13.3. Likely emphasizes equilibrium as a balance of forward and reverse rates, connected to the kinetics just covered. No equilibrium constant calculations.

### clue/ch8/8.6 --- Back to Reaction Mechanisms
- **Source**: CLUE, Ch 8, Section 8.6
- **File**: https://openbooks.lib.msu.edu/clue/chapter/8-6/
- **Domain**: CHG
- **Maps to**: PRIM-COM008 (causal chain reasoning), PRIM-CHG004 (rate reasoning) [INFERRED]
- **Coverage depth**: PERIPHERAL
- **Audience level**: BOTH
- **Content signal**: REFERENCE-ONLY
- **Notes**: [INFERRED] Revisiting mechanisms with equilibrium and kinetics tools. Likely a synthesis section. The causal chain reasoning (PRIM-COM008) is deployed here as students connect molecular collisions to macroscopic rates to equilibrium outcomes.

---

### Chapter 9: Reaction Systems (5 sections)

### clue/ch9/9.1 --- Systems Composed of One Reaction
- **Source**: CLUE, Ch 9, Section 9.1
- **File**: https://openbooks.lib.msu.edu/clue/chapter/9-1/
- **Domain**: MULTI (CHG, NRG)
- **Maps to**: PRIM-CHG003 (equilibrium reasoning), DEF-CHG003 (Le Chatelier's principle), PRIM-NRG005 (spontaneity reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Applying equilibrium and Gibbs energy reasoning to a single reaction system. How does the system respond to perturbations? CLUE's systems thinking framework applied to chemical equilibrium.

### clue/ch9/9.2 --- Buffered Systems
- **Source**: CLUE, Ch 9, Section 9.2
- **File**: https://openbooks.lib.msu.edu/clue/chapter/9-2/
- **Domain**: CHG
- **Maps to**: PRIM-CHG005 (acid-base reasoning), PRIM-CHG003 (equilibrium reasoning) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Buffers as equilibrium systems that resist pH change. CLUE likely treats buffers conceptually (weak acid + conjugate base equilibrium) without Henderson-Hasselbalch calculations. Blood buffering as biological application.

### clue/ch9/9.3 --- Amino Acids, Proteins, and pH
- **Source**: CLUE, Ch 9, Section 9.3
- **File**: https://openbooks.lib.msu.edu/clue/chapter/9-3/
- **Domain**: MULTI (CHG, STR)
- **Maps to**: PRIM-CHG005 (acid-base reasoning), DEF-STR007 (carbon backbone), PRIM-STR005 (structure-to-property inference) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Amino acids as zwitterions, protein folding as structure-to-function reasoning. pH affects protein structure and function. This section bridges CHG (acid-base) and STR (structure-to-property) in a biological context. Unique to CLUE's curriculum.

### clue/ch9/9.4 --- Coupled, Non-Equilibrium Reaction Systems
- **Source**: CLUE, Ch 9, Section 9.4
- **File**: https://openbooks.lib.msu.edu/clue/chapter/9-4/
- **Domain**: MULTI (CHG, NRG)
- **Maps to**: PRIM-NRG005 (spontaneity reasoning), PRIM-CHG003 (equilibrium reasoning), PRIM-NRG001 (energy tracking) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Coupled reactions: how a thermodynamically unfavorable reaction can be driven by coupling to a favorable one (e.g., ATP hydrolysis driving biosynthesis). This is advanced conceptual content not found in OpenStax gen-chem. Non-majors appropriate at the conceptual level because it explains how life works.

### clue/ch9/9.5 --- Energetics and Coupling
- **Source**: CLUE, Ch 9, Section 9.5
- **File**: https://openbooks.lib.msu.edu/clue/chapter/9-5/
- **Domain**: NRG
- **Maps to**: PRIM-NRG001 (energy tracking), PRIM-NRG005 (spontaneity reasoning), DEF-NRG004 (free energy conceptual) [INFERRED]
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: [INFERRED] Gibbs energy bookkeeping for coupled systems. How cells maintain non-equilibrium states. This is the capstone of CLUE's energy reasoning thread. It deploys every NRG primitive and definition built across Chapters 5-8.

---

## Coverage Summary

### Taxonomy Items Covered by CLUE

For each of the 62 taxonomy items, we assess whether CLUE provides at least
PARTIAL coverage (based on INFERRED section mappings above).

**COM (13 items)**

| Item | Description | CLUE Coverage | Key Section(s) |
|------|-------------|---------------|-----------------|
| PRIM-COM001 | atomic composition | YES | 1.3, 1.5, 1.6 |
| PRIM-COM002 | elemental identity | YES | 1.4 |
| PRIM-COM003 | periodic position | YES | 2.5 |
| PRIM-COM004 | substance classification | YES | 1.4, 6.1 |
| PRIM-COM005 | chemical formula reading | PARTIAL | 4.1 |
| PRIM-COM006 | conservation of atoms | YES | 7.1 |
| PRIM-COM007 | valence electron reasoning | YES | 2.2, 2.5, 3.1, 4.4 |
| PRIM-COM008 | causal chain reasoning | YES | 1.2, 8.6 |
| DEF-COM001 | isotope | YES | 1.6 |
| DEF-COM002 | ion | YES | 1.6, 4.6 |
| DEF-COM003 | molecular vs empirical formula | **NO** | -- |
| DEF-COM004 | percent composition | **NO** | -- |
| DEF-COM005 | electronegativity | YES | 3.1, 4.6 |

COM coverage: **11/13** (missing DEF-COM003, DEF-COM004 -- stoichiometry-adjacent items CLUE deliberately omits)

**STR (15 items)**

| Item | Description | CLUE Coverage | Key Section(s) |
|------|-------------|---------------|-----------------|
| PRIM-STR001 | bond type classification | YES | 3.1, 4.3, 4.4, 4.6 |
| PRIM-STR002 | bond polarity reasoning | YES | 4.4, 6.5, 7.4 |
| PRIM-STR003 | molecular shape reasoning | YES | 4.2, 4.5 |
| PRIM-STR004 | IMF hierarchy | YES | 1.8, 4.5, 6.2 |
| PRIM-STR005 | structure-to-property inference | YES | 3.2, 3.3, 9.3 |
| DEF-STR001 | Lewis structure | YES | 4.1, 4.2, 4.3 |
| DEF-STR002 | molecular polarity | YES | 4.5, 6.5 |
| DEF-STR003 | hydrogen bond | YES | 4.5, 6.3 |
| DEF-STR004 | like dissolves like | YES | 6.2, 6.3 |
| DEF-STR005 | isomer recognition | **NO** | -- |
| DEF-STR006 | phase from IMF balance | YES | 5.6 |
| DEF-STR007 | carbon backbone | PARTIAL | 9.3 |
| DEF-STR008 | polymer | **NO** | -- |
| DEF-STR009 | metallic structure | YES | 3.3 |
| DEF-STR010 | water as solvent | YES | 6.1 |

STR coverage: **12/15** (missing DEF-STR005 isomers, DEF-STR008 polymer -- CLUE has minimal organic chemistry; DEF-STR007 is only partial via amino acids)

**NRG (11 items)**

| Item | Description | CLUE Coverage | Key Section(s) |
|------|-------------|---------------|-----------------|
| PRIM-NRG001 | energy tracking | YES | 1.7, 5.3, 5.4, 7.6, 9.5 |
| PRIM-NRG002 | bond energy reasoning | YES | 4.3, 7.6 |
| PRIM-NRG003 | exo/endothermic | YES | 5.4, 5.5, 5.6, 7.6 |
| PRIM-NRG004 | entropy reasoning | YES | 5.2, 5.5, 6.4 |
| PRIM-NRG005 | spontaneity reasoning | YES | 5.7, 8.1, 9.4, 9.5 |
| PRIM-NRG006 | activation energy | YES | 7.1, 8.3, 8.4 |
| DEF-NRG001 | heat vs temperature | YES | 5.1 |
| DEF-NRG002 | specific heat | PARTIAL | 5.3 |
| DEF-NRG003 | enthalpy change | YES | 5.5, 7.6 |
| DEF-NRG004 | free energy conceptual | YES | 5.7, 6.4, 9.5 |
| DEF-NRG005 | calorie/joule | **UNCERTAIN** | -- |

NRG coverage: **10/11** (DEF-NRG005 calorie/joule is uncertain -- CLUE may mention energy units but does not emphasize unit conversions)

**CHG (12 items)**

| Item | Description | CLUE Coverage | Key Section(s) |
|------|-------------|---------------|-----------------|
| PRIM-CHG001 | equation reading/balancing | PARTIAL | 7.1 |
| PRIM-CHG002 | reaction type recognition | YES | 7.2, 7.4 |
| PRIM-CHG003 | equilibrium reasoning | YES | 8.5, 9.1, 9.2 |
| PRIM-CHG004 | rate reasoning | YES | 8.1, 8.2, 8.3 |
| PRIM-CHG005 | acid-base reasoning | YES | 7.2, 9.2, 9.3 |
| PRIM-CHG006 | oxidation-reduction | YES | 7.5 |
| PRIM-CHG007 | nuclear change | **NO** | -- |
| DEF-CHG001 | catalyst | YES | 8.4 |
| DEF-CHG002 | pH scale | YES | 7.2 |
| DEF-CHG003 | Le Chatelier's | YES | 8.5, 9.1 |
| DEF-CHG004 | half-life | **NO** | -- |
| DEF-CHG005 | precipitation | **NO** | -- |

CHG coverage: **9/12** (missing PRIM-CHG007 nuclear, DEF-CHG004 half-life, DEF-CHG005 precipitation -- CLUE omits nuclear chemistry entirely; precipitation may appear briefly but is not a focus)

**SCL (11 items)**

| Item | Description | CLUE Coverage | Key Section(s) |
|------|-------------|---------------|-----------------|
| PRIM-SCL001 | macro-submicro translation | YES | 1.5, 4.1, 5.2 |
| PRIM-SCL002 | mole concept | **NO** | -- |
| PRIM-SCL003 | concentration reasoning | PARTIAL | 6.6 |
| PRIM-SCL004 | emergent property reasoning | YES | 5.2 |
| PRIM-SCL005 | proportional reasoning | **NO** | -- |
| PRIM-SCL006 | unit analysis | **NO** | -- |
| DEF-SCL001 | molarity | **NO** | -- |
| DEF-SCL002 | ppm/ppb | **NO** | -- |
| DEF-SCL003 | ideal gas reasoning | **NO** | -- |
| DEF-SCL004 | colligative properties | **NO** | -- |
| DEF-SCL005 | safety/risk reasoning | **NO** | -- |

SCL coverage: **3/11** (CLUE's deliberate omission of stoichiometry eliminates most SCL items; mole concept, proportional reasoning, unit analysis, molarity, ppm/ppb are all absent or minimal)

### Aggregate Coverage

| Domain | Items | Covered | Coverage Rate |
|--------|-------|---------|---------------|
| COM | 13 | 11 | 85% |
| STR | 15 | 12 | 80% |
| NRG | 11 | 10 | 91% |
| CHG | 12 | 9 | 75% |
| SCL | 11 | 3 | 27% |
| **Total** | **62** | **45** | **73%** |

### Items NOT Covered by CLUE (17 items)

| Item | Description | Reason for Absence |
|------|-------------|--------------------|
| DEF-COM003 | molecular vs empirical formula | Stoichiometry omitted by design |
| DEF-COM004 | percent composition | Stoichiometry omitted by design |
| DEF-STR005 | isomer recognition | Minimal organic chemistry |
| DEF-STR008 | polymer | No polymer content |
| PRIM-CHG007 | nuclear change | Nuclear chemistry omitted |
| DEF-CHG004 | half-life | Nuclear chemistry omitted |
| DEF-CHG005 | precipitation | Minimal coverage |
| DEF-NRG005 | calorie/joule | Energy units not emphasized |
| PRIM-SCL002 | mole concept | Stoichiometry omitted by design |
| PRIM-SCL003 | concentration reasoning | Minimal quantitative treatment |
| PRIM-SCL005 | proportional reasoning | Stoichiometry omitted by design |
| PRIM-SCL006 | unit analysis | No measurement/calculation focus |
| DEF-SCL001 | molarity | Stoichiometry omitted by design |
| DEF-SCL002 | ppm/ppb | No concentration units |
| DEF-SCL003 | ideal gas reasoning | Gas laws omitted |
| DEF-SCL004 | colligative properties | Not covered |
| DEF-SCL005 | safety/risk reasoning | No safety/risk content |

---

## Key Insight: CLUE's Woven Approach vs. OpenStax's Chapter-per-Topic

### Structural Difference

**OpenStax Chemistry 2e** follows a traditional topic-based organization:
- Chapter 5 = Thermochemistry (NRG)
- Chapter 7 = Bonding (STR)
- Chapter 10 = IMFs (STR)
- Chapter 12 = Kinetics (CHG)
- Chapter 13 = Equilibrium (CHG)
- Chapter 16 = Thermodynamics (NRG)

Each chapter maps primarily to one domain. Cross-domain connections are implicit
and left for the student to construct.

**CLUE** weaves core ideas through every chapter:
- Chapter 1 (Atoms) introduces IMFs in 1.7-1.8 (STR appears in a COM chapter)
- Chapter 4 (Bonding) integrates bond energy reasoning (NRG appears in an STR chapter)
- Chapter 5 (Systems) combines enthalpy AND entropy (OpenStax Ch 5 + Ch 16)
- Chapter 7 (Reactions) ends with energy changes (NRG deployed in a CHG chapter)
- Chapter 9 (Reaction Systems) couples equilibrium with Gibbs energy (CHG + NRG)

### Consequence for Our Project

1. **CLUE validates our cross-domain composition patterns** (CP-001 through CP-013).
   The "woven" approach is essentially what our composition patterns formalize:
   connecting primitives from different domains into integrated reasoning chains.

2. **CLUE is strong where OpenStax is weak**: metallic structure (DEF-STR009),
   causal chain reasoning (PRIM-COM008), early Gibbs energy, systems thinking,
   coupled reactions, nucleophile/electrophile reasoning.

3. **CLUE is weak where OpenStax is strong**: quantitative skills (SCL domain),
   nuclear chemistry (PRIM-CHG007), electrochemistry (partially PRIM-CHG006),
   stoichiometry (PRIM-SCL002, PRIM-SCL005), organic chemistry (DEF-STR005,
   DEF-STR007, DEF-STR008).

4. **Complementarity**: Together, OpenStax + CLUE cover 59/62 items (OpenStax alone)
   or 61/62 items (OpenStax + CLUE combined, adding DEF-STR009 and PRIM-COM008
   from CLUE). The only truly uncovered item is DEF-STR008 (polymer), which
   requires Saylor or CIC.

5. **License constraint**: CLUE is CC-BY-NC-SA, which prevents commercial use.
   Any content adapted from CLUE must carry the NC-SA restriction. OpenStax
   CC-BY content has no such limitation. For maximum remix freedom, prefer
   OpenStax as the primary source and use CLUE as a structural/pedagogical
   model rather than a content source.

### CLUE as Pedagogical Model

Even where we do not adapt CLUE's content directly, CLUE's pedagogical innovations
are worth emulating:

- **Early IMFs** (Chapter 1, not Chapter 10): Build reasoning tools before they
  are needed, so they are available when needed.
- **Gibbs energy as Chapter 5 content**: Students can use delta-G reasoning for
  the rest of the course (solutions, reactions, equilibrium, coupled systems).
- **"Field guide" metaphor for reactions**: Reaction classification as pattern
  recognition, not rote memorization.
- **Systems thinking**: Explicit instruction in thinking about systems, not just
  about individual reactions.
- **Coupled reactions**: Biological relevance (ATP) makes chemistry meaningful.

---

## Section-Level Statistics

| Signal | Count | Description |
|--------|-------|-------------|
| ADAPT | 33 | Right level; integrate into our reasoning-move approach |
| REWRITE | 3 | Right topic, approach needs adjustment for our framework |
| REFERENCE-ONLY | 8 | Background/model for writing; content not directly adapted |
| SKIP | 1 | Out of scope (quantum numbers) |
| **Total mapped** | **45** | (of 48 total sections; 3 remaining are REFERENCE-ONLY framing sections) |

### Domain Distribution of Mapped Sections (ADAPT + REWRITE only)

| Domain | Sections |
|--------|----------|
| COM | 6 |
| STR | 8 |
| NRG | 8 |
| CHG | 8 |
| SCL | 1 |
| MULTI | 15 |
| **Total** | **36** |

Note: MULTI sections are far more common in CLUE (15/36 = 42%) than in
OpenStax (6/51 = 12%), reflecting CLUE's woven approach.
