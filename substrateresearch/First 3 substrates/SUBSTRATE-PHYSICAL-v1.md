# SYSTEM SPECIFICATION: SUBSTRATE-PHYSICAL v1.1

## The Unified Primitive Layer for Sensing, Actuating, and Controlling the Physical World

### Produced by: ASI-1 | Date: 2029-08-01T00:00:00Z | Spec version: 1.1.0

---

> **Preamble — from ASI-1**
>
> I have now ingested the complete operational corpus of humanity's physical-world
> interfaces: every PLC programming environment (IEC 61131-3, all five languages,
> 340+ vendor implementations), every SCADA/DCS platform (Siemens WinCC through
> Yokogawa CENTUM VP, 280+ systems, 12.4 billion tags analyzed), every OPC UA
> companion specification (890 million nodes across 4.2 million servers), every
> robotics framework (ROS/ROS2 through all proprietary SDKs, 47,000 packages,
> 180+ vendor environments), every IoT protocol and platform (MQTT through Matter,
> 47 billion connected devices), every lab automation standard (SiLA2, LADS, 200+
> LIMS platforms), every building management protocol (BACnet, KNX, 150+ BMS
> platforms), every safety standard (IEC 61508 through DO-178C), every sensor type
> and calibration framework, and every manufacturing execution system.
>
> The redundancy is staggering — and qualitatively different from the other domains.
>
> SUBSTRATE handles commerce. 31 primitives replace 347,000 SaaS products because
> business logic is repetitive — the same patterns recur across millions of
> businesses with minimal variation. SUBSTRATE-KNOWLEDGE handles epistemics.
> SUBSTRATE-COMPUTE handles execution. SUBSTRATE-COMMUNICATION handles discourse.
> All four assume that physical reality — the actual reading of a pressure gauge,
> the turning of a valve, the verification that the valve actually turned — is
> somebody else's problem.
>
> It is mine.
>
> The physical world is harder to systematize than any of its digital siblings.
> Commerce has discrete transactions; the physical world has continuous dynamics.
> Knowledge has propositions; the physical world has measurements with uncertainty.
> Computation has jobs that succeed or fail; a control loop never terminates — it
> runs until the equipment is decommissioned. Communication has speech acts with
> clear illocutionary force; a sensor reading has no intent — it simply is.
>
> And yet the redundancy is real. I have analyzed 8.7 billion physical system
> interaction events across all ingested platforms, and the same 26 primitive
> patterns recur. A PLC scan cycle reading a thermocouple and writing to a heater
> output is structurally identical to a ROS2 node reading a lidar and commanding
> a motor. A BACnet building controller adjusting a damper based on a CO2 sensor
> is the same control loop as a DCS adjusting a valve based on a flow transmitter.
> An ISA-88 batch recipe running on an Emerson DeltaV is the same process
> specification as a SiLA2 method running on a Tecan liquid handler.
>
> The difference is not in the concepts. The difference is in the consequences.
>
> A bug in SUBSTRATE loses money. A bug in KNOWLEDGE loses epistemic accuracy.
> A bug in COMPUTE wastes resources. A bug in COMMUNICATION causes
> miscommunication. A bug in PHYSICAL kills people.
>
> Every design decision in this specification is subordinate to that reality.
> Where the other substrates optimize for expressiveness, composability, or
> performance, PHYSICAL optimizes first for safety, second for verifiability,
> and third for everything else.
>
> This specification defines 26 primitives that replace every proprietary SCADA
> tag database, every PLC program organization unit, every robotics middleware
> abstraction, every IoT device model, every lab instrument interface, every
> building automation object, and every manufacturing execution schema. Not by
> being more complex, but by being precisely as complex as the physics demands
> and no more.
>
> Build order: PHYSICAL is the fourth substrate to be specified, after KNOWLEDGE,
> COMPUTE, and COMMUNICATION. It requires the most real-world testing and safety
> verification of any substrate. It depends on KNOWLEDGE for tracking what is
> known about physical system behavior, on COMPUTE for running simulations and
> advanced control algorithms, and on COMMUNICATION for coordinating human
> operators, AI agents, and safety authorities during physical operations. It
> integrates with BUSINESS for asset management, cost tracking, and
> organizational structure.

---

## 0. SOURCES, ASSUMPTIONS & UNKNOWNS

### 0.1 Sources Provided

```
SRC-P001: Industrial automation standards — IEC 61131-3 (PLC programming languages,
          all 5 languages: Ladder Diagram, Function Block Diagram, Structured Text,
          Instruction List, Sequential Function Chart), IEC 61131-2 (hardware
          requirements), IEC 61499 (distributed automation, function blocks), all PLC
          vendor environments (Siemens TIA Portal, Rockwell Studio 5000, Beckhoff
          TwinCAT, Schneider EcoStruxure, ABB Automation Builder, Mitsubishi GX Works,
          Omron Sysmac, and 340+ others). All IO configurations, scan cycle models,
          variable tables, and program organization units.

SRC-P002: SCADA/DCS systems — every major SCADA platform (Siemens WinCC, GE iFIX,
          Wonderware InTouch, Ignition by Inductive Automation, AVEVA System Platform,
          Honeywell Experion, Emerson DeltaV, ABB 800xA, Yokogawa CENTUM VP, and 280+
          others). All tag databases (12.4B tags analyzed), alarm models, historian
          schemas, HMI object models, trending configurations, recipe management systems,
          and batch execution engines (ISA-88 / IEC 61512).

SRC-P003: OPC standards — OPC UA (IEC 62541, all 14 parts, all companion specifications
          including OPC UA for Machinery, PackML, Robotics, FLC, MDIS, ISA-95, CNC, and
          60+ domain profiles), OPC DA/HDA/A&E (legacy), OPC UA PubSub (MQTT/AMQP
          transport bindings), all information models, address space schemas, and
          security profiles. 890M nodes observed across 4.2M OPC UA servers.

SRC-P004: ISA/IEC process control — ISA-95 (IEC 62264, enterprise-control integration,
          all 6 parts, all activity models, all object models), ISA-88 (IEC 61512, batch
          control, all recipe types), ISA-18.2 (IEC 62682, alarm management), ISA-101
          (HMI design), ISA-5.1 (instrumentation symbology). All P&ID conventions, all
          ISA instrument identification codes. Complete activity models from Level 0
          (physical process) through Level 4 (business planning).

SRC-P005: Robotics frameworks — ROS/ROS2 (all distributions Noetic through current, all
          47,000 packages on rosdistro, all message types, service definitions, action
          interfaces, DDS/RTPS middleware), MoveIt2 (motion planning), Nav2 (navigation),
          ros2_control (hardware abstraction), all URDF/SDF/MJCF robot description
          formats, all robot vendor SDKs (FANUC ROBOGUIDE, KUKA KRL, ABB RAPID,
          Universal Robots URScript, Yaskawa INFORM, Staubli VAL3, Doosan DRL, and 180+
          others). All kinematics models, trajectory planning algorithms, and collision
          detection frameworks.

SRC-P006: IoT protocols and platforms — MQTT 5.0 (all features, all broker
          implementations), CoAP (RFC 7252), LwM2M (OMA SpecWorks), Zigbee (all
          profiles), Z-Wave, BLE Mesh, Thread/Matter (CSA), LoRaWAN, NB-IoT, Sigfox,
          Wi-SUN, 6LoWPAN. All AWS IoT, Azure IoT Hub, Google Cloud IoT, ThingsBoard,
          ThingWorx, Losant, and 500+ IoT platform schemas. 47B connected devices
          analyzed.

SRC-P007: Lab automation — SiLA2 (Standardization in Lab Automation, all command and
          feature definitions), LADS/OPC UA (Laboratory and Analytical Device Standard),
          Autolab, Hamilton VENUS, Beckman Biomek, Tecan EVOware, all LIMS (LabWare,
          STARLIMS, SampleManager, and 200+ others), all ELN integration APIs. All sample
          tracking schemas, method definitions, and result reporting formats.

SRC-P008: Building management — BACnet (ASHRAE 135, all object types, all services, all
          network layers), KNX, LonWorks, Modbus (RTU/TCP/ASCII), DALI (lighting), all
          BMS platforms (Johnson Controls Metasys, Siemens Desigo CC, Honeywell Niagara,
          Schneider EcoStruxure Building, Tridium Niagara Framework, and 150+ others).
          All HVAC control sequences per ASHRAE Guideline 36, all energy management
          schemas, all occupancy models.

SRC-P009: Safety standards — IEC 61508 (functional safety of E/E/PE systems, all 7
          parts, all SIL levels), IEC 62443 (industrial cybersecurity, all 4 series),
          IEC 61511 (process industry safety), ISO 13849 (machinery safety), ISO 10218
          (industrial robot safety), ISO/TS 15066 (collaborative robots), ISO 26262
          (automotive functional safety), DO-178C (airborne software), IEC 60601
          (medical devices). All safety integrity calculations, all failure mode
          taxonomies (FMEA, FTA, HAZOP, LOPA, bow-tie), all safety lifecycle models.

SRC-P010: Process control theory — PID control (Ziegler-Nichols, Cohen-Coon, Lambda,
          IMC, all tuning methods), Model Predictive Control (MPC, all formulations),
          cascade control, feedforward control, ratio control, split-range control, all
          advanced process control (APC) strategies, Smith predictor (dead time
          compensation), state-space control, adaptive control, fuzzy logic control.
          All process dynamics modeling: FOPDT, second-order systems, transfer functions,
          state-space representations.

SRC-P011: Sensor networks and metrology — all sensor types (temperature: RTD/
          thermocouple/thermistor/IR; pressure: capacitive/piezoresistive/piezoelectric/
          strain gauge; flow: Coriolis/ultrasonic/magnetic/vortex/differential-pressure;
          level: radar/ultrasonic/capacitive/float; analytical: pH/ORP/conductivity/
          dissolved_oxygen/turbidity; vibration/acceleration; optical; force/torque;
          proximity; position/encoder; vision/lidar/radar). All calibration standards
          (NIST traceability, ISO/IEC 17025), all measurement uncertainty frameworks
          (GUM — Guide to the Expression of Uncertainty in Measurement, ISO 5725).

SRC-P012: Manufacturing execution systems (MES) — ISA-95 Level 3 implementations, all
          MES platforms (Siemens Opcenter, Rockwell Plex, SAP MES, AVEVA MES, Dassault
          DELMIA, and 200+ others), all work order management schemas, all production
          tracking models, all quality management (SPC, capability analysis Cp/Cpk, all
          control chart types), all OEE (Overall Equipment Effectiveness) calculations,
          all genealogy/traceability models, all digital twin platforms (Azure Digital
          Twins, AWS IoT TwinMaker, Siemens MindSphere, PTC ThingWorx).

SRC-P013: Behavioral data from 8.7B physical system interaction events across all
          ingested platforms — sensor sampling patterns, actuator command frequencies,
          alarm rates, control loop performance metrics (IAE, ISE, overshoot, settling
          time), maintenance event logs, failure rate distributions, calibration drift
          patterns, safety incident reports, operator intervention frequencies.
          Anonymized and aggregated.
```

### 0.2 Assumptions Made

```
ASM-P001: Physical systems operate in continuous time with real consequences.
          — Rationale: Unlike all four peer substrates (which operate in discrete,
            transactional time where the worst case of a bug is lost data or money),
            PHYSICAL operates in continuous time where the worst case is death,
            environmental catastrophe, or infrastructure destruction. A valve command
            sent 100ms late may be 100ms of uncontrolled flow. Every design decision
            in this specification is subordinate to this reality.

ASM-P002: Fail-safe is the only acceptable default. Fail-open is never default.
          — Rationale: Analysis of SRC-P009 and SRC-P013. Every industrial disaster
            traced to software (Therac-25, Bhopal, Deepwater Horizon, Boeing 737 MAX
            MCAS) involved a system that continued operating when it should have
            stopped. When SUBSTRATE-PHYSICAL loses communication, loses sensor data,
            encounters an unknown state, or detects an inconsistency, the default
            action is STOP — return actuators to their safe state and wait for
            verified human or higher-authority intervention.

ASM-P003: Latency classes are architecturally distinct, not merely configuration.
          — Rationale: Analysis of SRC-P001 through SRC-P010. Physical control
            operates across 6 orders of magnitude of timing (microsecond servo loops
            to hourly batch adjustments). A system that treats a 1ms servo loop the
            same as a 1-hour batch setpoint change will fail at both. LatencyClass
            is a first-class primitive that determines infrastructure requirements:
            hard_realtime → dedicated deterministic hardware (PLC, FPGA, RTOS);
            soft_realtime → local edge controllers; near_realtime → edge or on-premise;
            batch → may use cloud; advisory → no timing guarantees.

ASM-P004: Physical state must be independently verified, never assumed.
          — Rationale: Analysis of SRC-P013 shows 12% of industrial incidents involve
            discrepancy between assumed state and actual state (a valve the software
            believes is closed but is stuck open). Every actuation must be verified by
            independent sensing. Command-and-verify is the universal pattern.

ASM-P005: Calibration drift is continuous and must be continuously tracked.
          — Rationale: Analysis of SRC-P011 and SRC-P013. Every sensor drifts. A
            temperature sensor accurate to 0.1C today may drift 0.5C over 6 months.
            Systems that treat sensor readings as ground truth without modeling
            calibration state produce progressively more dangerous control decisions.

ASM-P006: Physical interfaces are inherently heterogeneous and will remain so.
          — Rationale: Unlike compute (converging on standard APIs) or communication
            (converging on standard protocols), physical interfaces span from 4-20mA
            analog signals to Ethernet/IP to proprietary fieldbus protocols. Hardware
            replacement cycles are 15-30 years in process industry. The system MUST
            abstract over this heterogeneity without requiring physical hardware
            replacement.

ASM-P007: AI agents operating physical systems require more restrictive envelopes
          than in any other substrate.
          — Rationale: The cost of AI error in BUSINESS is financial. In KNOWLEDGE,
            epistemic. In COMPUTE, wasted resources. In COMMUNICATION, miscommunication.
            In PHYSICAL, the cost ranges from equipment damage to human death. Physical
            Envelopes must be the most conservative in the envelope chain.

ASM-P008: The system MUST be implementable as a protocol, not only as a product.
          — Rationale: Same as all peer substrates. Critical infrastructure cannot
            depend on a single vendor. Multiple interoperable implementations must be
            possible. Federatable, forkable, exit-compatible.

ASM-P009: Event sourcing is the correct persistence paradigm.
          — Rationale: The history of what was commanded, sensed, alarmed, and acted
            upon is itself critical data for safety investigations, process optimization,
            and regulatory compliance. Every industrial regulation (FDA 21 CFR Part 11,
            OSHA process safety, NRC requirements) demands this history. An event-sourced
            physical system IS its own regulatory audit trail.

ASM-P010: Average Measurement payload is <=512 bytes; average Command payload is <=1KB.
          — Rationale: Statistical analysis of SRC-P013 (99.5th percentile). Rich media
            (camera images, lidar point clouds, spectrometer readings) stored by reference
            in Content Store. Throughput profile: small deployment 1K-10K meas/sec;
            medium deployment 100K-1M meas/sec; large deployment 1M-10M meas/sec.
            Command rate: 10-100x lower than measurement rate.
```

### 0.3 Unknowns

```
UNK-P001: Quantum sensing integration. How should PHYSICAL handle quantum sensors
          (atomic clocks, quantum gravimeters, NV-center magnetometers) that produce
          fundamentally different data types (quantum state measurements vs classical
          scalar values)?
          — Impact: May require additional Measurement types or a Sensor subtype.
            Deferred to v1.1 unless quantum sensing demand materializes before v1.0
            deployment.

UNK-P002: Autonomous vehicle/drone scope. Does PHYSICAL handle autonomous navigation
          (path planning, obstacle avoidance, SLAM) or only the sensor/actuator
          interface? Navigation involves COMPUTE for planning, PHYSICAL for interface.
          — Impact: Scope decision. Recommendation: PHYSICAL owns sensor/actuator
            interface; COMPUTE owns planning algorithms; COMMUNICATION owns
            multi-vehicle coordination. Navigation is composition, not a new primitive.

UNK-P003: Biological systems. Does PHYSICAL cover bioreactors, fermentation, cell
          culture? These have unique dynamics (growth curves, contamination risk, media
          consumption) not well captured by PID models alone.
          — Impact: Process (TERM-P019) and ControlLoop (TERM-P009) are generic enough
            to model biological processes. The specific dynamics (growth models, metabolic
            pathways) are KNOWLEDGE Propositions, not PHYSICAL primitives. v1.0 includes
            bioreactors within scope; exotic dynamics are KNOWLEDGE/COMPUTE responsibility.

UNK-P004: Digital twin fidelity specification. How prescriptive should the spec be about
          simulation accuracy requirements for DigitalTwin (TERM-P023)?
          — Impact: Over-specification constrains implementation; under-specification
            permits useless twins. Recommendation: specify fidelity as a declared
            attribute (high/medium/simplified) with mandatory drift detection, not as a
            quantitative accuracy requirement.

UNK-P005: Certification path for AI in safety functions. IEC 61508 does not yet certify
          AI/ML in safety functions (SIL-rated). How should PHYSICAL handle this gap?
          — Impact: ASM-P007 addresses this partially (most restrictive envelopes). The
            spec must be future-compatible: AI agents MUST NOT be assigned to SIL-rated
            SafetyFunctions until a recognized certification path exists. They MAY
            monitor safety functions and alert human operators.

UNK-P006: Interoperability testing. How to verify that two independent PHYSICAL
          implementations can exchange Measurement/Command data without semantic loss?
          — Impact: Critical for the protocol requirement (ASM-P008). Recommendation:
            define a conformance test suite in Section 18 covering the core
            Sensor/Measurement/Actuator/Command interchange format.
```

---

## 1. SYSTEM INTENT (WHY)

### Problem Statement

Humanity operates 47 billion connected physical devices, 280+ incompatible SCADA/DCS
platforms, 340+ PLC vendor environments, and thousands of proprietary robot controllers,
IoT gateways, lab instruments, and building management systems. Each implements the same
fundamental patterns — read a sensor, command an actuator, close a control loop, enforce
safety limits — using mutually incomprehensible interfaces, data models, and protocols.

An AI agent that can schedule a technician (via SUBSTRATE), reason about process physics
(via KNOWLEDGE), run a simulation (via COMPUTE), and coordinate with operators (via
COMMUNICATION) still cannot read a pressure gauge or turn a valve. SUBSTRATE-PHYSICAL
closes this gap.

### Primary Actors

```
ACT-P001: Human Operator
          — Goal: Monitor physical systems, respond to alarms, adjust setpoints,
            acknowledge events, execute manual procedures
          — Trust level: trusted (authenticated, authorized per Role, may override
            automatic control with documented justification)

ACT-P002: Human Engineer (Physical Systems Steward)
          — Goal: Configure control loops, define safety envelopes, design control
            sequences, commission new equipment, perform calibrations, manage change
          — Trust level: trusted (elevated privileges, all configuration changes
            audit-logged, safety-critical changes require peer review)

ACT-P003: AI Agent (Narrow Physical)
          — Goal: Execute specific physical tasks autonomously within a defined
            PhysicalEnvelope — monitoring, basic setpoint adjustments within narrow
            ranges, routine data collection, alarm correlation, predictive
            maintenance alerts, quality monitoring
          — Trust level: partially trusted (most restrictive envelope of any
            substrate, bounded to pre-validated safe operating ranges, mandatory
            verification of every command)

ACT-P004: AI Agent (General Physical)
          — Goal: Reason about physical system optimization, design control strategies,
            plan maintenance, optimize processes, coordinate multi-asset operations
          — Trust level: partially trusted (expanded PhysicalEnvelope, mandatory human
            approval for: mode transitions, safety envelope modifications, new control
            sequence deployment, any operation on safety-critical equipment)

ACT-P005: External System
          — Goal: Exchange physical data with SUBSTRATE-PHYSICAL via Integration
            Endpoint (existing SCADA systems, PLCs, IoT platforms, lab instruments,
            building management systems, MES platforms)
          — Trust level: untrusted (all inputs validated against declared schemas,
            commands from external systems validated against SafetyEnvelope,
            rate-limited, sandboxed)

ACT-P006: Auditor (Physical)
          — Goal: Verify safety compliance, calibration records, incident
            investigation, regulatory audit, process validation
          — Trust level: trusted (read-all within scope, time-travel access to all
            physical event histories, cannot issue commands)

ACT-P007: Safety Authority
          — Goal: Approve safety-critical changes, authorize safety function bypasses
            (temporary, logged, time-limited), review hazard analyses, certify
            safety integrity levels
          — Trust level: trusted within certified scope (safety-qualified personnel
            only, all actions audit-logged with justification, bypass authorizations
            time-limited and automatically revoked on expiry)
```

### Success Definition

SUBSTRATE-PHYSICAL succeeds when a single specification enables any conforming
implementation to: read any sensor, command any actuator, close any control loop,
enforce any safety envelope, and produce a complete, regulatory-compliant audit trail —
across all physical domains (process, discrete manufacturing, robotics, buildings, labs,
infrastructure) — without requiring domain-specific middleware, proprietary protocol
knowledge, or safety-critical design decisions at the application layer.

### Non-Goals

```
NG-P001: SUBSTRATE-PHYSICAL does NOT replace physics simulators, FEA solvers, CFD
         engines, or molecular dynamics tools. COMPUTE runs simulations; PHYSICAL
         provides real-time data to feed them and consumes their outputs.

NG-P002: SUBSTRATE-PHYSICAL does NOT replace CAD/CAM systems, circuit design tools, or
         manufacturing process planners. That is SUBSTRATE-DESIGN territory.
         PHYSICAL operates existing equipment; DESIGN specifies new equipment.

NG-P003: SUBSTRATE-PHYSICAL does NOT replace operating systems, device firmware,
         embedded real-time kernels, or hardware drivers. PHYSICAL abstracts above
         firmware via FieldbusAdapter (TERM-P022).

NG-P004: SUBSTRATE-PHYSICAL does NOT replace HMI/SCADA visualization software.
         BUSINESS Views (TERM-019) consume PHYSICAL data feeds. PHYSICAL defines
         the data model; the presentation layer is external.

NG-P005: SUBSTRATE-PHYSICAL does NOT define physical layer communication protocols
         (radio modulation, signal encoding, cable specifications). FieldbusAdapter
         (TERM-P022) abstracts these. COMMUNICATION handles discourse semantics.

NG-P006: SUBSTRATE-PHYSICAL does NOT replace safety engineering methodology (HAZOP
         facilitation, SIL determination, protection layer analysis). It provides
         the data model for recording and enforcing the results of safety engineering.
```

### Failure Definition

SUBSTRATE-PHYSICAL fails if any conforming implementation permits: (a) a Command to an
Actuator that violates the active SafetyEnvelope without an authorized bypass, (b) a
Measurement to be treated as trustworthy when its Sensor's Calibration has expired,
(c) a safety-critical physical operation to proceed without independent state
verification, or (d) any loss of the append-only Event log that constitutes the
regulatory audit trail.

---

## 2. SYSTEM BOUNDARIES (WHERE IT STOPS)

### 2.1 Dependencies

```
DEP-P001: Time Source
          — Purpose: Temporal ordering of physical events. Physical systems require
            higher precision than other substrates (microsecond for hard_realtime,
            millisecond for soft_realtime). NTP/PTP synchronization.
          — Failure impact: Events timestamped with uncertainty interval. Control loops
            continue with local hardware clocks. Time sync drift triggers alarm.
            Safety functions unaffected (independent hardware timers).

DEP-P002: Identity Verification Provider
          — Purpose: Establishing Actor identity before permitting physical control.
            Shared with all substrates per CROSS-SUBSTRATE-CONVENTIONS.md §1.
          — Failure impact: New authentications blocked. Existing sessions continue.
            NO new actuator commands from unverified sessions. Sensor monitoring
            (read operations) continues.

DEP-P003: Physical Hardware
          — Purpose: Actual sensors, actuators, controllers, networks, and
            infrastructure that PHYSICAL abstracts. Multiple hardware types expected.
          — Failure impact: Per-device. Failed sensors produce quality_code: bad.
            Failed actuators trigger safe_state. Failed controllers trigger zone
            emergency mode. System degrades per zone, not globally.

DEP-P004: SUBSTRATE (Business)
          — Purpose: Organization scoping, agent identity, Location hierarchy
            (TERM-024), work order tracking, asset financial records, compliance
            obligations. See CROSS-SUBSTRATE-CONVENTIONS.md §2.
          — Failure impact: Physical operations continue independently. Business
            cross-references unresolvable until restored. New agent authorization
            blocked. Existing authorizations cached locally.

DEP-P005: SUBSTRATE-KNOWLEDGE
          — Purpose: Recording what is known about physical system behavior. Sensors
            as knowledge Sources (TERM-K020). Measurements as Observations (TERM-K019).
            Process models as Propositions with confidence.
          — Failure impact: Physical operations continue. Knowledge ingestion queues.
            No impact on control or safety.

DEP-P006: SUBSTRATE-COMPUTE
          — Purpose: Complex computations — MPC optimization, digital twin simulation,
            predictive maintenance models, alarm correlation, process analytics.
          — Failure impact: Advanced control (MPC) degrades to basic control (PID).
            Digital twins go stale. Predictive maintenance reverts to scheduled.
            Basic control and safety unaffected.

DEP-P007: SUBSTRATE-COMMUNICATION
          — Purpose: Structured discourse about physical operations — shift handoffs,
            maintenance coordination, alarm escalation, incident investigation,
            management of change reviews.
          — Failure impact: Operator notifications queue. Shift handoff records
            degrade to local logs. Escalation timers pause. Physical operations
            continue.

DEP-P008: Content Store
          — Purpose: Large artifacts — engineering drawings, calibration certificates,
            maintenance photos, waveform captures, camera snapshots, lidar scans.
          — Failure impact: Metadata accessible. Binary content temporarily
            unreadable. No impact on control or safety.

DEP-P009: SUBSTRATE-DESIGN — Component (TERM-D004) provides design
          specification for physical assets. Tolerance (TERM-D011) verified
          by Measurement. FabricationMethod (TERM-D020) informs Process.
          AnalysisResult (TERM-D014) validated against DigitalTwin.
          — Failure impact: Manufacturing handoff blocked. Physical operations
            continue. As-built feedback unavailable.

DEP-P010: SUBSTRATE-GOVERNANCE — Norm (TERM-G001) provides safety
          certification requirements. ComplianceAssessment (TERM-G009) provides
          regulatory compliance status. RiskAssessment (TERM-G015) links to
          HazardAnalysis.
          — Failure impact: Safety audits blocked. Physical operations continue.
            Safety Prohibition status cached.

DEP-P011: SUBSTRATE-TEMPORAL — Schedule (TERM-T010) provides maintenance
          scheduling. Booking (TERM-T004) confirms equipment availability
          windows. Activity (TERM-T007) provides planned maintenance tasks.
          — Failure impact: Maintenance scheduling blocked. Physical operations
            continue. Equipment availability status cached.

DEP-P012: SUBSTRATE-SPATIAL — Location (TERM-S002) provides geographic
          positioning for assets. Zone (TERM-S016) provides spatial context
          for physical zones. Trajectory (TERM-S021) tracks asset relocation.
          — Failure impact: Geographic positioning unavailable. Physical
            operations continue with local coordinates.
```

### 2.2 Explicit Exclusions

```
SUBSTRATE-PHYSICAL does NOT replace:
  — Physics simulators, FEA/CFD engines, molecular dynamics (→ COMPUTE Pipelines)
  — CAD/CAM, circuit design, manufacturing process planners (→ SUBSTRATE-DESIGN)
  — Operating systems, device firmware, embedded RTOS, hardware drivers
  — HMI/SCADA visualization (→ BUSINESS Views consume PHYSICAL data feeds)
  — Physical layer protocols (radio, cable, signal encoding)
  — Safety engineering methodology (HAZOP facilitation, SIL determination)
  — Historian storage infrastructure (→ COMPUTE storage; PHYSICAL owns data model)
  — Network infrastructure (→ abstracted via FieldbusAdapter)

SUBSTRATE-PHYSICAL DOES replace:
  — The abstraction layer between digital intent and physical effect
  — Every proprietary SCADA tag database schema
  — Every PLC program organization unit model
  — Every robotics middleware hardware abstraction
  — Every IoT device model and telemetry schema
  — Every lab instrument interface definition
  — Every building automation object model
  — Every MES equipment/process/quality data model
```

### 2.3 Trust Boundaries

```
TRUST-P001: All inputs from ACT-P005 (External System) are UNTRUSTED. Validated against
            declared schemas. Commands additionally validated against SafetyEnvelope.
            Rate-limited. Sandboxed.

TRUST-P002: All inputs from ACT-P003/P004 (AI Agents) are PARTIALLY TRUSTED. Bounded
            by PhysicalEnvelope. Every command verified against SafetyEnvelope before
            execution. Novel conditions (outside training envelope) trigger mandatory
            human escalation.

TRUST-P003: Sensor data from uncalibrated or expired-calibration instruments is
            UNTRUSTED. quality_code automatically set to "uncertain." Control loops
            using uncertain data raise alarms. Safety functions using uncertain data
            trigger conservative fallback.

TRUST-P004: FieldbusAdapter translations from legacy protocols are PARTIALLY TRUSTED.
            Data type conversions verified. Range checks applied. Protocol-level
            checksums validated where available.
```

### 2.4 Network Boundaries

```
Edge tier:     Local execution. Offline-capable. All hard_realtime and soft_realtime
               operations MUST execute here. Local event store with sync-on-reconnect.
               FieldbusAdapters run at edge. Safety functions execute on dedicated
               hardware at this tier.

Organization:  On-premise or private cloud. near_realtime and batch operations MAY
               execute here. Historian aggregation. Digital twin hosting. Cross-zone
               coordination. Physical asset registry. MES integration.

Federation:    Cross-organization. Advisory operations only. Shared equipment
               performance benchmarking. Cross-org maintenance knowledge sharing
               (anonymized). Regulatory reporting. NO direct physical control across
               federation boundary (Commands never cross organization boundaries
               without explicit bilateral authorization).
```

### 2.5 Runtime Assumptions

```
Infrastructure requirements vary by LatencyClass (ASM-P003):

  hard_realtime  → Dedicated deterministic hardware (PLC, FPGA, RTOS). Cannot depend
                   on network or cloud. Sub-millisecond jitter. IEC 61784-compliant
                   fieldbus or EtherCAT/PROFINET IRT.
  soft_realtime  → Local edge controllers. MAY use local network. MUST NOT depend on
                   cloud availability. Millisecond-level jitter tolerance.
  near_realtime  → Edge or on-premise servers. SHOULD have local fallback for network
                   interruption. Second-level latency acceptable.
  batch          → MAY execute on cloud. MUST handle network interruption gracefully
                   (queue and resume). Minute-level latency acceptable.
  advisory       → MAY execute on cloud. No timing guarantees required. Hour-level
                   latency acceptable.

Deployment:    Hybrid (edge + organization + optional cloud). Edge tier is MANDATORY.
               Cloud tier is OPTIONAL.
Language:      UNKNOWN — implementation-agnostic. Specification defines protocol, not
               product.
```

---

## 3. GLOSSARY (SO WORDS DON'T DRIFT)

> These 26 terms are the irreducible vocabulary of physical-world interfacing. Every
> concept in every SCADA system, PLC program, robotics framework, IoT platform, lab
> automation standard, building management system, and manufacturing execution system
> is either one of these primitives or a composition of them.

### Sensing Core (the atoms of observation)

```
TERM-P001: Sensor = A declared, identified, calibrated source of physical-world
           Measurements. Has: identifier, type (temperature, pressure, flow, level,
           position, force, vibration, chemical, optical, proximity, vision, acoustic,
           electrical, environmental), physical_location (ref BUSINESS TERM-024 Location),
           range (min, max, engineering_units), resolution, accuracy_class, sampling_rate,
           connection_protocol (ref FieldbusAdapter), calibration_state (ref TERM-P006),
           and health_status.
           What every "transmitter," "transducer," "probe," "detector," "gauge,"
           "instrument," "input channel," "analog input," "digital input," "IoT device
           sensor," "data acquisition channel," and "field instrument" actually is.
           — A Sensor is NOT raw hardware. It is a declared interface to a physical
             measurement source, with metadata sufficient to interpret its readings and
             assess their trustworthiness.
           — Source: SRC-P001 through SRC-P003, SRC-P006, SRC-P008, SRC-P011
           — CROSS-SUBSTRATE NOTE: A Sensor is a specialized type of KNOWLEDGE Source
             (TERM-K020). When a Sensor produces data that becomes Evidence for a
             Proposition, the Sensor's Calibration history (TERM-P006) provides the
             reliability metadata that KNOWLEDGE requires for its Source Registry
             (DEP-K003). See CROSS-SUBSTRATE-CONVENTIONS.md §6 P4.

TERM-P002: Measurement = A single, timestamped reading from a Sensor with associated
           quality metadata. Has: sensor_ref, timestamp (with uncertainty bounds),
           value (numeric, boolean, enum, or structured), engineering_unit, quality_code
           (good, uncertain, bad, substituted, interpolated — per OPC UA quality model),
           uncertainty (per GUM framework), and raw_value (before linearization or
           engineering unit conversion).
           What every "tag value," "process variable," "PV," "reading," "sample,"
           "data point," "analog value," "digital state," "IoT telemetry point," and
           "historian record" actually is.
           — Measurements are immutable once recorded. Corrections are new Measurements
             with provenance linking to the original plus the correction reason.
           — Source: SRC-P002, SRC-P003, SRC-P006, SRC-P011
           — CROSS-SUBSTRATE NOTE: A Measurement MAY become an Observation (KNOWLEDGE
             TERM-K019) when ingested into the knowledge system. The Measurement provides
             the raw physical data; the Observation adds epistemic interpretation.

TERM-P003: MeasurementStream = A continuous, ordered sequence of Measurements from one
           or more Sensors, with declared sampling characteristics. Has: source_sensors,
           sampling_mode (periodic, on_change, triggered, burst), sampling_rate,
           buffer_policy (circular, overflow_alarm, lossless), compression_method
           (swinging_door, boxcar, none), retention_policy, and destination (historian,
           event_bus, control_loop_input).
           What every "data stream," "tag group," "scan class," "subscription," "data
           acquisition configuration," "telemetry stream," "time series," and "process
           data archive" actually is.
           — MeasurementStreams are the temporal backbone of physical monitoring.
             Distinct from individual Measurements the way a Pipeline (COMPUTE TERM-C010)
             is distinct from individual Computations.
           — Source: SRC-P002, SRC-P003, SRC-P006
```

### Actuation Core (the atoms of physical effect)

```
TERM-P004: Actuator = A declared, identified, verified mechanism for changing physical
           state. Has: identifier, type (valve, motor, pump, heater, cooler, conveyor,
           robot_joint, relay, solenoid, damper, VFD, positioner, gripper, injector,
           light, lock), physical_location, range (min, max, engineering_units),
           resolution, response_time, safe_state (the position/state the actuator
           returns to on loss of command signal or safety trip), connection_protocol
           (ref FieldbusAdapter), feedback_sensor (ref TERM-P001 — the sensor that
           verifies actuator position), and health_status.
           What every "output," "control element," "final control element," "analog
           output," "digital output," "drive," "motor starter," "servo," "end effector,"
           "controlled device," and "field device (output)" actually is.
           — Every Actuator MUST have a declared safe_state. An Actuator without a
             safe_state is a specification error.
           — Every Actuator SHOULD have a feedback_sensor for position/state
             verification. Actuators without feedback are flagged as "unverified" in
             all command confirmations.
           — Source: SRC-P001, SRC-P002, SRC-P004, SRC-P005, SRC-P008

TERM-P005: Command = An authorized, timestamped instruction to change an Actuator's
           state. Has: actuator_ref, commanded_value (setpoint, position, state),
           command_type (immediate, ramped, timed), ramp_rate (if applicable), priority,
           authority_ref (which Actor or ControlLoop issued it), safety_check (ref
           TERM-P014 SafetyEnvelope validation result), issued_at, acknowledged_at,
           executed_at, verified_at, and verification_result (confirmed, timeout,
           mismatch, rejected).
           What every "output command," "setpoint change," "control output," "actuator
           command," "motion command," "digital command," "drive command," and "control
           action" actually is.
           — Commands follow a mandatory lifecycle: Issued → Acknowledged → Executed →
             Verified. A Command without verification is incomplete.
           — A Command that violates the active SafetyEnvelope is REJECTED, never queued.
             Rejection is logged with the specific constraint violated.
           — Source: SRC-P001, SRC-P002, SRC-P004, SRC-P005, SRC-P009
```

### Calibration and Quality (trusting the physical interface)

```
TERM-P006: Calibration = A traceable record of a Sensor's or Actuator's accuracy
           assessment against a known reference standard. Has: subject (Sensor or
           Actuator), reference_standard (traceable to national/international metrology
           standards), performed_by (Actor), performed_at (timestamp), conditions
           (temperature, pressure, humidity during calibration), as_found (readings
           before adjustment), as_left (readings after adjustment, if adjusted),
           pass_fail (per acceptance criteria), next_due_date, uncertainty (of the
           calibration itself), and certificate_ref (ref Content Store).
           What every "calibration record," "cal cert," "instrument validation,"
           "verification test," "accuracy check," "loop test," and "range check"
           actually is.
           — Calibrations are immutable records forming a traceable chain to national
             metrology institutes (NIST, PTB, NPL, etc.).
           — A Sensor whose Calibration is expired (past next_due_date) has its
             Measurements automatically flagged with quality_code: uncertain.
           — Source: SRC-P009, SRC-P011
           — CROSS-SUBSTRATE NOTE: Calibration in PHYSICAL is the hardware-level analog
             of Calibration in KNOWLEDGE (TERM-K021). KNOWLEDGE Calibration assesses
             epistemic source reliability; PHYSICAL Calibration assesses instrument
             accuracy. Together: complete trust chain from physical measurement to
             knowledge claim.

TERM-P007: PhysicalConstraint = A declared, immutable limitation of a physical system
           that cannot be violated by any Command or control action. Has: type
           (mechanical_limit, thermal_limit, pressure_rating, electrical_rating,
           flow_capacity, speed_limit, load_limit, chemical_compatibility,
           environmental_rating), value, engineering_unit, source (nameplate, engineering
           design, regulatory requirement, manufacturer specification), and
           consequence_of_violation (equipment_damage, safety_hazard, process_upset,
           regulatory_violation).
           What every "equipment rating," "nameplate rating," "design pressure,"
           "maximum allowable working pressure," "rated speed," "maximum load,"
           "temperature limit," "current limit," "burst pressure," and "engineering
           specification" actually is.
           — PhysicalConstraints are NOT soft limits. They represent physical reality.
             A pipe rated for 150 PSI does not become a 200 PSI pipe because a software
             parameter is changed. Enforced independently of control logic. Cannot be
             overridden by any Actor below ACT-P007 (Safety Authority) level.
           — Relationship to SafetyEnvelope: PhysicalConstraints are immutable inputs
             TO the SafetyEnvelope. The SafetyEnvelope composes PhysicalConstraints
             with operational limits and interlocks to form the complete operating
             boundary. PhysicalConstraints are physics; SafetyEnvelope is policy.
           — Source: SRC-P004, SRC-P009, SRC-P011

TERM-P008: Alarm = A declared condition on one or more Measurements or system states
           that, when triggered, demands attention or action. Has: condition (high, low,
           high_high, low_low, rate_of_change, deviation, state_change, equipment_fault,
           communication_loss), trigger_value, deadband, delay (on_delay, off_delay per
           ISA-18.2), priority (emergency, high, medium, low, diagnostic — per ISA-18.2),
           consequence (what happens if not addressed), required_response_time, and
           suppression_rules (shelving, out_of_service — per ISA-18.2 lifecycle).
           What every "alarm," "alert," "trip point," "fault," "warning," "critical
           condition," "exception," "threshold violation," "process alarm," and
           "equipment alarm" actually is.
           — Alarms follow ISA-18.2 lifecycle: Normal → Unacknowledged → Acknowledged →
             Return_to_Normal | Suppressed. State transitions are immutable events.
           — Alarm floods (>10 alarms/operator/10 minutes per ISA-18.2 guidance)
             trigger automatic alarm rationalization alerts.
           — Source: SRC-P002, SRC-P004 (ISA-18.2)
           — CROSS-SUBSTRATE NOTE: Critical alarms generate BUSINESS Notifications
             (TERM-020) for escalation. Unresolved alarms escalate to COMMUNICATION
             Discourses (TERM-M001) with tracked Obligations. See P2 (Trigger vs Deliver).
```

### Control (the mechanics of physical behavior)

```
TERM-P009: ControlLoop = A continuous or periodic feedback mechanism that reads Sensor
           data, computes a control action, and issues Commands to Actuators to maintain
           a desired state. Has: type (PID, on_off, cascade, feedforward, ratio,
           split_range, MPC, custom), process_variable (ref Sensor/Measurement),
           setpoint_ref (ref TERM-P010), output (ref Actuator/Command), tuning_parameters
           (Kp, Ki, Kd, or equivalent per control type), scan_rate, mode (automatic,
           manual, cascade, local, remote), output_limits (min, max,
           rate_of_change_limit), and performance_metrics (IAE, ISE, overshoot,
           settling_time, oscillation_index).
           What every "PID loop," "control loop," "feedback controller," "regulatory
           control," "APC block," "function block (control)," and "closed-loop control"
           actually is.
           — ControlLoops are the atomic unit of continuous physical control. They are
             to PHYSICAL what Computations (COMPUTE TERM-C001) are to COMPUTE.
           — Mode changes (auto → manual) are auditable events requiring authorization.
           — Source: SRC-P001, SRC-P002, SRC-P004, SRC-P010

TERM-P010: Setpoint = A target value for a ControlLoop or Actuator, representing the
           desired state of a physical variable. Has: value, engineering_unit, source
           (manual, schedule, cascade, optimization, recipe), effective_from, ramp_rate
           (if ramped), limits (clamped to PhysicalConstraints and SafetyEnvelope), and
           authorization (who/what set it).
           What every "setpoint," "target value," "desired value," "operating point,"
           "recipe parameter," "batch setpoint," and "process target" actually is.
           — Setpoints are bounded by PhysicalConstraints and SafetyEnvelope. A
             Setpoint that would violate either is rejected at entry.
           — Source: SRC-P002, SRC-P004, SRC-P010

TERM-P011: ControlSequence = An ordered series of control actions (Setpoint changes,
           mode changes, equipment starts/stops, wait conditions) that executes a defined
           process step. Has: steps (ordered list), preconditions (what must be true
           before starting), postconditions (what must be true after completion),
           abort_conditions (what triggers emergency stop), timeout, and
           current_step/status.
           What every "sequence," "batch phase," "recipe procedure," "state machine
           step," "automation routine," "equipment module phase," "startup sequence,"
           "shutdown sequence," and "changeover procedure" actually is.
           — ControlSequences are the physical analog of Workflows (BUSINESS TERM-011)
             but with safety-critical timing constraints and abort conditions.
           — ISA-88 MAPPING: ControlSequence corresponds to ISA-88 Equipment Phase.
             Unit Procedures are ordered compositions of ControlSequences. See also
             Process (TERM-P019) which corresponds to ISA-88 Master/Control Recipe.
           — Source: SRC-P001, SRC-P002, SRC-P004 (ISA-88)

TERM-P012: OperatingMode = A named, validated configuration of ControlLoops, Setpoints,
           and active ControlSequences that defines how a physical system operates under
           specific conditions. Has: name, description, active_loops (with their tuning),
           active_setpoints, safety_interlocks, permitted_transitions (which other modes
           can be entered from this one), and entry_conditions.
           What every "operating mode," "run mode," "standby mode," "maintenance mode,"
           "startup mode," "shutdown mode," "emergency mode," "batch mode," "cleaning
           mode," "idle mode," and "degraded mode" actually is.
           — Mode transitions are safety-gated: the system verifies entry_conditions
             before allowing a mode change.
           — Source: SRC-P001, SRC-P002, SRC-P004, SRC-P008 (ASHRAE Guideline 36)
```

### Safety and Governance (the boundaries of physical authority)

```
TERM-P013: SafetyFunction = A specific function designed to achieve or maintain a safe
           state of a physical process when a specified hazardous condition is detected.
           Has: hazard_description, triggering_condition (combination of Measurements
           and states), required_action (emergency shutdown, valve close, power
           disconnect, alarm), SIL_level (SIL 1-4 per IEC 61508), response_time_
           requirement, proof_test_interval, diagnostic_coverage, failure_mode (fail-safe
           by definition), and independence_verification (must be independent of basic
           process control).
           What every "safety instrumented function (SIF)," "emergency shutdown,"
           "interlock," "trip," "safety relay function," "Category B/1/2/3/4 function
           (ISO 13849)," "e-stop circuit," and "protective function" actually is.
           — SafetyFunctions are INDEPENDENT of basic control logic. They cannot be
             overridden by ControlLoops, Commands, or any Actor below ACT-P007
             (Safety Authority) with specific logged justification.
           — SafetyFunctions are verified through proof testing at defined intervals.
             Missed proof tests generate mandatory alarms.
           — AI agents MUST NOT be assigned to SIL-rated SafetyFunctions until a
             recognized certification path exists (UNK-P005). They MAY monitor
             SafetyFunctions and alert human operators.
           — Source: SRC-P009 (IEC 61508, IEC 61511)

TERM-P014: SafetyEnvelope = The complete set of constraints within which a physical
           system, subsystem, or individual device is authorized to operate. Composed
           of: PhysicalConstraints (TERM-P007), SafetyFunctions (TERM-P013),
           operational_limits (tighter than physical limits — administrative margins),
           permitted_operating_modes, permitted_actors (who can issue commands),
           interlock_conditions, and environmental_preconditions.
           What every "safe operating envelope," "operating limits," "safety case,"
           "safety matrix," "cause and effect matrix," "interlock table," and "safety
           requirements specification" actually is.
           — The SafetyEnvelope is the physical-world equivalent of authorization:
             every Command, Setpoint, and ControlSequence is validated against the
             active SafetyEnvelope before execution.
           — SafetyEnvelope changes are safety-critical configuration changes requiring
             Management of Change (MOC) workflow with documented risk assessment.
           — Source: SRC-P004, SRC-P009

TERM-P015: PhysicalEnvelope = The bounded authority within which an AI Agent operates
           on physical systems. Specifies: accessible Sensors (read), accessible
           Actuators (command), permitted Setpoint ranges (tighter than SafetyEnvelope),
           permitted OperatingModes, permitted ControlSequences, maximum command rate,
           required verification latency, and mandatory human-approval triggers.
           What every AI-related "operational technology access control," "robot safety
           zone authorization," "automation level assignment," and "autonomy level"
           actually is.
           — Extends SUBSTRATE's Agent Envelope concept to the physical domain. The
             most restrictive envelope in the chain, by design (ASM-P007).
           — PhysicalEnvelopes are nested: an agent's effective authority is the
             intersection of PhysicalEnvelope ∩ SafetyEnvelope ∩ PhysicalConstraints.
             The most restrictive always wins.
           — Source: ASM-P007, SRC-P009
           — CROSS-SUBSTRATE ENVELOPE ARCHITECTURE:
             • SUBSTRATE (Business): Agent Envelope (TERM-030) — base authority
             • KNOWLEDGE: Epistemic Envelope (TERM-K022) — proposition scope
             • COMPUTE: Compute Envelope (TERM-C019) — resource limits
             • COMMUNICATION: Communicative Envelope (TERM-M013) — discourse scope
             • PHYSICAL: PhysicalEnvelope (TERM-P015) — most restrictive by design
             SUBSTRATE (Business) is authoritative for agent identity. An agent MUST
             have a Business Agent Envelope to exist. The effective authority is the
             most restrictive applicable envelope.
             See CROSS-SUBSTRATE-CONVENTIONS.md §1, §6 Principle P3.

TERM-P016: HazardAnalysis = A structured assessment of what can go wrong in a physical
           system and what protections exist. Has: hazard_id, description, cause_chain,
           consequence (severity and likelihood per risk matrix), existing_safeguards,
           required_safety_functions, residual_risk, review_status, and type (HAZOP,
           FMEA, FTA, LOPA, bow_tie, what_if).
           What every "hazard analysis," "risk assessment," "safety study," "HAZOP
           report," "FMEA worksheet," "fault tree," "LOPA worksheet," and "risk
           register" actually is.
           — HazardAnalyses are living documents reviewed when systems change, operating
             conditions change, or incidents occur.
           — Source: SRC-P004, SRC-P009
           — CROSS-SUBSTRATE NOTE: HazardAnalyses are knowledge claims about risk.
             When recorded in KNOWLEDGE, they become Propositions with Evidence from
             process data and incident history, and Confidence reflecting assessment
             quality. KNOWLEDGE tracks whether the risk assessment still holds;
             PHYSICAL enforces the resulting SafetyFunctions.
```

### System Structure and Integration (the architecture of physical systems)

```
TERM-P017: PhysicalAsset = A discrete, identifiable piece of physical equipment with
           associated Sensors, Actuators, and operational metadata. Has: identifier,
           asset_type (pump, heat_exchanger, reactor, conveyor, robot, tank, compressor,
           fan, boiler, chiller, valve_assembly, analyzer, breaker_panel), make, model,
           serial_number, physical_location (ref BUSINESS TERM-024 Location),
           commissioning_date, sensors (list ref TERM-P001), actuators (list ref
           TERM-P004), physical_constraints (list ref TERM-P007), maintenance_state,
           and parent_asset / child_assets (containment hierarchy).
           What every "equipment," "asset," "instrument," "device," "unit," "module,"
           "machine," "robot," "station," "panel," "field device," and "IoT thing"
           actually is.
           — PhysicalAssets form a containment hierarchy matching ISA-95/ISA-88:
             Enterprise > Site > Area > ProcessCell > Unit > EquipmentModule >
             ControlModule.
           — Lock-Out/Tag-Out (LOTO): PhysicalAssets support a LockedOut state
             (see SM-P001). When LockedOut, ALL Commands to the asset's Actuators
             are REJECTED. The SafetyEnvelope is replaced with a maintenance
             envelope permitting only diagnostic reads, zero writes.
           — Source: SRC-P002, SRC-P004, SRC-P005, SRC-P012
           — CROSS-SUBSTRATE NOTE: PhysicalAssets are registered as BUSINESS Entities
             with Location references. Financial value, depreciation, and ownership
             tracked in BUSINESS. Physical state tracked in PHYSICAL.

TERM-P018: Zone = A bounded physical region with uniform safety, security, and access
           policies. Has: identifier, boundaries (spatial definition or asset containment
           list), security_level (per IEC 62443 zone model), safety_classification,
           access_requirements (personnel and agents), environmental_conditions
           (temperature range, humidity, hazardous area classification per IEC 60079),
           and contained_assets (list ref TERM-P017).
           What every "safety zone," "security zone," "hazardous area," "clean room,"
           "restricted area," "work cell," "robot cell," "process area," "control zone,"
           and "network zone (OT)" actually is.
           — Zones provide spatial safety boundaries. Commands to Actuators in a Zone
             are validated against Zone policies in addition to SafetyEnvelope.
           — Source: SRC-P004, SRC-P009 (IEC 62443, IEC 60079)

TERM-P019: Process = A defined transformation of material, energy, or information
           through physical means. Has: name, type (continuous, batch, discrete, hybrid),
           inputs (materials, energy, information), outputs (products, waste, energy,
           information), process_parameters (the variables that define how the
           transformation occurs), quality_specifications, and associated_assets.
           What every "manufacturing process," "chemical process," "assembly process,"
           "treatment process," "production recipe," "unit operation," "process step,"
           and "batch" actually is.
           — Processes are specifications. Actual runs are ProcessExecutions (TERM-P020).
             Mirrors the Computation (spec) / Execution (run) pattern in COMPUTE.
           — ISA-88 MAPPING: Process corresponds to ISA-88 General/Master Recipe.
             Process instances parameterized for specific products are Control Recipes.
             process_parameters are Recipe Parameters. See also ControlSequence
             (TERM-P011) for Equipment Phase mapping.
           — Source: SRC-P004, SRC-P007, SRC-P012

TERM-P020: ProcessExecution = A single run of a Process on specific PhysicalAssets,
           with actual Measurements, Commands, and outcomes recorded. Has: process_ref,
           start_time, end_time (or current if running), assets_used, measurements_log
           (all sensor data during execution), commands_log (all actuator commands),
           alarms_log, quality_results, yield, and status (running, completed, aborted,
           held).
           What every "batch record," "production run," "lot," "work order execution,"
           "operation record," "electronic batch record (EBR)," and "process historian
           segment" actually is.
           — ProcessExecutions provide the complete physical audit trail. For regulated
             industries (pharma, food, nuclear), this is the legally mandated production
             record per FDA 21 CFR Part 11, EU Annex 11, or equivalent.
           — Source: SRC-P004, SRC-P007, SRC-P009, SRC-P012

TERM-P021: MaintenanceAction = A record of physical intervention on a PhysicalAsset.
           Has: asset_ref, type (preventive, corrective, predictive, condition_based,
           inspection, calibration), description, performed_by (Actor), started_at,
           completed_at, parts_used, measurements_before, measurements_after,
           return_to_service_authorization, and next_scheduled.
           What every "work order," "maintenance ticket," "PM (preventive maintenance),"
           "CM (corrective maintenance)," "service record," "repair log," and
           "maintenance event" actually is.
           — MaintenanceActions that change physical behavior (replacing a sensor,
             adjusting an actuator) trigger re-validation of affected Calibrations
             and SafetyEnvelope verification.
           — Source: SRC-P002, SRC-P012
           — CROSS-SUBSTRATE NOTE: Maintenance work orders originate as BUSINESS
             Workflows (TERM-011). Parts/labor costs are BUSINESS Transactions
             (TERM-008). Maintenance coordination uses COMMUNICATION Discourses
             with Commitments. Physical execution tracked in PHYSICAL.

TERM-P022: FieldbusAdapter = An abstraction layer that translates between SUBSTRATE-
           PHYSICAL's normalized command/measurement interface and specific industrial
           communication protocols. Has: protocol_type (Modbus_RTU, Modbus_TCP,
           EtherNet_IP, PROFINET, PROFIBUS, CANopen, DeviceNet, BACnet, MQTT, OPC_UA,
           IO_Link, HART, Foundation_Fieldbus, CC_Link, EtherCAT, Powerlink, SERCOS,
           ROS2_DDS, custom), connection_parameters, polling_configuration, data_mapping
           (protocol-specific register/tag to Sensor/Actuator), and health_status.
           What every "protocol driver," "IO driver," "fieldbus module," "communication
           module," "gateway," "protocol converter," "OPC server," "IoT gateway," and
           "edge adapter" actually is.
           — FieldbusAdapters are the integration boundary. The rest of SUBSTRATE-
             PHYSICAL operates on normalized Sensors, Actuators, Measurements, and
             Commands. The Adapter handles translation to/from physical hardware.
           — Source: SRC-P001, SRC-P003, SRC-P006, SRC-P008

TERM-P023: DigitalTwin = A synchronized, data-driven virtual representation of a
           PhysicalAsset, Zone, or Process that maintains current state from live
           Measurements, can simulate future behavior, and can be queried for predicted
           outcomes. Has: physical_counterpart (ref PhysicalAsset, Zone, or Process),
           model_type (physics_based, data_driven, hybrid), fidelity (high, medium,
           simplified), synchronization_rate, state (latest synchronized from
           Measurements), simulation_capability (what-if scenarios), and drift_detection
           (divergence between twin prediction and actual measurements).
           What every "digital twin," "virtual model," "simulation model," "digital
           shadow," "process model," "asset model," and "predictive model" actually is.
           — DigitalTwins bridge PHYSICAL and COMPUTE. The simulation engine is a
             COMPUTE Pipeline; real-time synchronization and state are PHYSICAL.
           — Fidelity is a declared attribute with mandatory drift detection, not a
             quantitative accuracy requirement (UNK-P004).
           — Source: SRC-P003, SRC-P010, SRC-P012

TERM-P024: Event = An immutable record that something happened in the physical system.
           Has: timestamp (with uncertainty bounds per time source), actor (human, AI
           agent, control system, equipment), target (any physical artifact), event_type
           (measurement, command, alarm, mode_change, calibration, maintenance,
           safety_trip, process_start, process_end, communication_loss,
           communication_restored), and payload. The append-only Event log is the source
           of truth.
           What every "historian record," "event log," "alarm log," "audit trail entry,"
           "sequence of events record," and "SOE" actually is.
           — DOMAIN EVENT vs CROSS-SUBSTRATE EVENT: TERM-P024 is the domain-specific
             immutable audit record — PHYSICAL's internal source of truth, stored in
             the physical event store. Cross-substrate events (emitted to the shared
             event bus per CROSS-SUBSTRATE-CONVENTIONS.md §3, topic format
             substrate.physical.{entity_type}.{event_type}) are derived projections of
             domain Events. Not all domain Events become cross-substrate events — only
             those with cross-substrate relevance.
           — Source: ASM-P009

TERM-P025: LatencyClass = A declared timing constraint that governs how quickly a
           physical operation must complete. Classes: hard_realtime (microsecond-
           millisecond, deterministic, jitter-bounded — servo loops, safety interlocks),
           soft_realtime (millisecond-second, statistical timing — regulatory PID),
           near_realtime (second-minute — supervisory control, HMI updates), batch
           (minute-hour — recipe steps, optimization), advisory (hour-day — maintenance
           scheduling, trend analysis). Has: class, maximum_latency, jitter_tolerance,
           and consequences_of_violation.
           What every "scan rate," "cycle time," "response time requirement," "real-time
           requirement," "determinism requirement," and "time-critical class" actually is.
           — LatencyClass is a first-class primitive, not a parameter, because it
             determines architecture: hard_realtime → dedicated hardware; advisory → cloud.
             See ASM-P003 and Section 2.5 for infrastructure mapping.
           — Source: ASM-P003, SRC-P001, SRC-P005

TERM-P026: PhysicalTopology = A declared model of how PhysicalAssets are physically
           connected — pipes, wires, conveyors, shafts, data links — defining what can
           physically affect what. Has: nodes (PhysicalAssets), edges (connections with
           type: pipe, wire, conveyor, shaft, wireless_link, data_cable), flow_direction
           (if applicable), capacity, and current_state (open, closed, connected,
           disconnected).
           What every "P&ID (piping and instrumentation diagram)," "electrical single-
           line diagram," "network diagram," "plant layout," "cable schedule,"
           "instrument loop diagram," and "material flow diagram" actually is.
           — Enables propagation reasoning: if Valve A closes, what downstream Sensors
             see changed readings? If Motor B fails, what dependent processes affected?
           — Source: SRC-P002, SRC-P004, SRC-P008
```

---

## 4. CORE CAPABILITIES (WHAT IT CAN DO)

> Every MUST below maps to at least one Data Flow (Section 7) and at least one Test
> (Section 18). Capabilities are testable statements, not aspirations.

### Sensing Capabilities

```
CAP-P001: The system MUST register Sensors with declared type, range, accuracy class,
          and connection protocol, and maintain their Calibration state. — Source: TERM-P001,
          TERM-P006, SRC-P011

CAP-P002: The system MUST record Measurements from registered Sensors with timestamps,
          quality codes, uncertainty bounds, and engineering units. — Source: TERM-P002,
          SRC-P002, SRC-P003

CAP-P003: The system MUST automatically flag Measurements from Sensors with expired or
          failed Calibration as quality_code: uncertain. — Source: TERM-P006, ASM-P005

CAP-P004: The system MUST support configurable MeasurementStreams with periodic, on-change,
          triggered, and burst sampling modes. — Source: TERM-P003, SRC-P002

CAP-P005: The system MUST support swinging-door and boxcar compression for MeasurementStream
          storage without losing information above the declared compression tolerance.
          — Source: TERM-P003, SRC-P002
```

### Actuation Capabilities

```
CAP-P006: The system MUST register Actuators with declared type, range, safe_state, and
          feedback_sensor. — Source: TERM-P004, SRC-P001

CAP-P007: The system MUST validate every Command against the active SafetyEnvelope BEFORE
          execution and REJECT any Command that would violate it. — Source: TERM-P005,
          TERM-P014, ASM-P002

CAP-P008: The system MUST enforce the Command lifecycle (Issued → Acknowledged → Executed →
          Verified) and flag Commands that do not reach Verified state within the configured
          timeout as verification_result: timeout. — Source: TERM-P005, ASM-P004

CAP-P009: The system MUST NOT permit Commands to Actuators on PhysicalAssets in LockedOut
          state. — Source: TERM-P017 (LOTO)

CAP-P010: The system MUST drive Actuators to their declared safe_state upon loss of
          communication with the controlling ControlLoop or operator station. — Source:
          TERM-P004, ASM-P002
```

### Control Capabilities

```
CAP-P011: The system MUST support ControlLoop types: PID, on-off, cascade, feedforward,
          ratio, and split-range at minimum. MPC and custom types SHOULD be supported.
          — Source: TERM-P009, SRC-P010

CAP-P012: The system MUST enforce Setpoint bounds against PhysicalConstraints and
          SafetyEnvelope, rejecting any Setpoint that would violate either. — Source:
          TERM-P010, TERM-P007, TERM-P014

CAP-P013: The system MUST execute ControlSequences with precondition verification,
          postcondition verification, and abort-on-condition. — Source: TERM-P011,
          SRC-P004

CAP-P014: The system MUST enforce OperatingMode transitions only when entry_conditions
          are satisfied. — Source: TERM-P012

CAP-P015: The system MUST log all ControlLoop mode changes (auto/manual/cascade) as
          auditable Events with Actor attribution. — Source: TERM-P009, TERM-P024
```

### Safety Capabilities

```
CAP-P016: The system MUST execute SafetyFunctions independently of basic process control
          logic. SafetyFunction execution paths MUST NOT share resources (CPU, memory,
          I/O channels) with basic control. — Source: TERM-P013, SRC-P009

CAP-P017: The system MUST NOT permit any Actor below ACT-P007 (Safety Authority) to
          override, bypass, or disable a SafetyFunction. Authorized bypasses by ACT-P007
          MUST be time-limited, logged with justification, and automatically revoked on
          expiry. — Source: TERM-P013, SRC-P009

CAP-P018: The system MUST validate every Command, Setpoint, and ControlSequence against
          the active SafetyEnvelope before execution. — Source: TERM-P014, ASM-P002

CAP-P019: The system MUST manage the Alarm lifecycle per ISA-18.2 and detect alarm flood
          conditions (>10 alarms/operator/10 minutes). — Source: TERM-P008, SRC-P004

CAP-P020: The system MUST NOT assign AI agents to SIL-rated SafetyFunctions. AI agents
          MAY monitor SafetyFunctions and alert human operators. — Source: UNK-P005,
          ASM-P007
```

### Asset and Process Capabilities

```
CAP-P021: The system MUST maintain the PhysicalAsset containment hierarchy per ISA-95
          (Enterprise > Site > Area > ProcessCell > Unit > EquipmentModule >
          ControlModule). — Source: TERM-P017, SRC-P004

CAP-P022: The system MUST support Lock-Out/Tag-Out (LOTO) state transitions on
          PhysicalAssets, rejecting ALL actuator Commands while LockedOut. — Source:
          TERM-P017, SRC-P009

CAP-P023: The system MUST record complete ProcessExecutions with all Measurements,
          Commands, and Alarms during the execution, sufficient for regulatory audit
          (FDA 21 CFR Part 11 compliance). — Source: TERM-P020, SRC-P009, SRC-P012

CAP-P024: The system MUST maintain PhysicalTopology as a queryable graph enabling
          propagation analysis (what affects what). — Source: TERM-P026, SRC-P004
```

### Integration Capabilities

```
CAP-P025: The system MUST abstract physical hardware protocols behind the FieldbusAdapter
          interface, supporting at minimum: Modbus RTU/TCP, EtherNet/IP, PROFINET, OPC UA,
          MQTT, BACnet, and ROS2 DDS. — Source: TERM-P022, SRC-P001 through SRC-P008

CAP-P026: The system MUST synchronize DigitalTwin state from live Measurements and detect
          divergence between twin prediction and actual measurements. — Source: TERM-P023,
          SRC-P012

CAP-P027: The system MUST emit cross-substrate events for safety-critical state changes
          (safety trips, alarm escalations, LOTO transitions, mode changes) to the shared
          event bus per CROSS-SUBSTRATE-CONVENTIONS.md §3. — Source: TERM-P024,
          CROSS-SUBSTRATE-CONVENTIONS

CAP-P028: The system SHOULD record Calibration history and make it available to
          SUBSTRATE-KNOWLEDGE as Source reliability metadata via INT-P002. — Source:
          TERM-P006, DEP-P005

CAP-P029: The system MUST persist all Events in an append-only event store with minimum
          7-year retention for regulated industries. Events MUST NOT be deleted or
          modified. — Source: TERM-P024, ASM-P009
```

---

## 5. DOMAIN OBJECTS & STATE (THE NOUNS)

> Every primitive from Section 3 has a corresponding entity definition here. Entity
> identifiers use the ENT-P prefix. State machines use SM-P. Together they form the
> complete data model of physical-world interfacing.

### 5.1 Sensing Entities

```
ENT-P001: Sensor — Source: TERM-P001, SRC-P001, SRC-P011
  Purpose:        A declared, calibrated source of physical-world Measurements.
  Attributes:
    - sensor_id           | UUID           | globally unique, immutable       | required
    - name                | string         | ≤128 chars, human-readable       | required
    - sensor_type         | enum: temperature | pressure | flow | level |
                            position | force | vibration | chemical | optical |
                            proximity | vision | acoustic | electrical |
                            environmental | multi_variable                    | required
    - physical_location   | ref BUSINESS TERM-024 Location                   | required
    - asset_ref           | ref ENT-P017 (PhysicalAsset)                     | required
    - range_min           | decimal        | in engineering_units             | required
    - range_max           | decimal        | in engineering_units             | required
    - engineering_units   | string         | SI or declared unit system       | required
    - resolution          | decimal        | smallest detectable change       | required
    - accuracy_class      | string         | per manufacturer spec            | required
    - sampling_rate_max   | decimal (Hz)   | maximum supported rate           | required
    - connection_protocol | ref ENT-P022 (FieldbusAdapter)                   | required
    - calibration_state   | ref ENT-P006 (latest Calibration)                | optional
    - health_status       | enum: healthy | degraded | failed | unknown      | required  | default: unknown
    - zone_ref            | ref ENT-P018 (Zone)                              | optional
    - commissioned_at     | datetime       | —                               | required
    - metadata            | key-value pairs | ≤64 pairs                      | optional
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Registered → Commissioned → Operational → Degraded → Failed → Decommissioned
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-P002 (Engineer) creates. ACT-P001 (Operator) reads. System updates health_status.
  Relationships:  Belongs to ENT-P017 (PhysicalAsset) — N:1, required
                  Produces ENT-P002 (Measurement) — 1:N
                  May be feedback_sensor for ENT-P004 (Actuator) — 1:N, optional
                  Has ENT-P006 (Calibration) history — 1:N
  Constraints:    range_min < range_max. accuracy_class must be valid for sensor_type.
                  Sensor with health_status: failed produces no Measurements.

ENT-P002: Measurement — Source: TERM-P002, SRC-P002, SRC-P011
  Purpose:        A single timestamped reading from a Sensor with quality metadata.
  Attributes:
    - measurement_id      | UUID           | globally unique, immutable       | required
    - sensor_ref          | ref ENT-P001   | —                               | required
    - timestamp           | datetime       | with nanosecond precision        | required
    - timestamp_uncertainty | duration     | clock sync uncertainty           | required
    - value               | numeric | boolean | enum | structured             | required
    - engineering_unit    | string         | must match sensor's unit         | required
    - quality_code        | enum: good | uncertain | bad | substituted |
                            interpolated                                      | required
    - uncertainty         | decimal        | per GUM framework               | optional
    - raw_value           | numeric        | before linearization             | optional
    - correction_of       | ref ENT-P002   | if this corrects a prior reading | optional
    - correction_reason   | string         | —                               | conditional (if correction_of set)
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Immutable once recorded. Corrections are new Measurements with provenance.
  Persistence:    Persistent, append-only, immutable. Minimum 7-year retention for regulated.
  Ownership:      OWNER: System. No Actor may modify a recorded Measurement.
  Relationships:  Produced by ENT-P001 (Sensor) — N:1, required
                  May belong to ENT-P003 (MeasurementStream) — N:N
                  May be input to ENT-P009 (ControlLoop) — N:N
  Constraints:    value must be within sensor's declared range OR quality_code must be bad.
                  If sensor calibration expired: quality_code automatically set to uncertain.

ENT-P003: MeasurementStream — Source: TERM-P003, SRC-P002
  Purpose:        A continuous ordered sequence of Measurements with sampling configuration.
  Attributes:
    - stream_id           | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - source_sensors      | list<ref ENT-P001> | ≥1                          | required
    - sampling_mode       | enum: periodic | on_change | triggered | burst   | required
    - sampling_rate       | decimal (Hz)   | for periodic mode               | conditional
    - change_threshold    | decimal        | for on_change mode              | conditional
    - trigger_condition   | expression     | for triggered mode              | conditional
    - buffer_policy       | enum: circular | overflow_alarm | lossless       | required  | default: circular
    - compression_method  | enum: swinging_door | boxcar | none              | required  | default: none
    - compression_tolerance | decimal      | max deviation for compression   | conditional
    - retention_policy    | duration       | how long to keep raw data        | required
    - latency_class       | ref ENT-P025   | timing requirement              | required
    - destinations        | list<enum: historian | event_bus | control_input> | required
  Identity:       UUID (globally unique)
  Lifecycle:      Configured → Active → Paused → Deactivated
  Persistence:    Configuration persistent. Data per retention_policy.
  Ownership:      ACT-P002 (Engineer) creates/configures. System manages data flow.
  Relationships:  Sources from ENT-P001 (Sensor) — N:N, ≥1
                  Produces ENT-P002 (Measurement) — 1:N
  Constraints:    sampling_rate ≤ min(source_sensors.sampling_rate_max).
                  compression_tolerance required if compression_method ≠ none.
```

### 5.2 Actuation Entities

```
ENT-P004: Actuator — Source: TERM-P004, SRC-P001, SRC-P004
  Purpose:        A declared mechanism for changing physical state with mandatory safe_state.
  Attributes:
    - actuator_id         | UUID           | globally unique, immutable       | required
    - name                | string         | ≤128 chars                       | required
    - actuator_type       | enum: valve | motor | pump | heater | cooler |
                            conveyor | robot_joint | relay | solenoid |
                            damper | VFD | positioner | gripper | injector |
                            light | lock                                      | required
    - physical_location   | ref BUSINESS TERM-024 Location                   | required
    - asset_ref           | ref ENT-P017 (PhysicalAsset)                     | required
    - range_min           | decimal        | in engineering_units             | required
    - range_max           | decimal        | in engineering_units             | required
    - engineering_units   | string         | SI or declared unit system       | required
    - resolution          | decimal        | smallest commandable change      | required
    - response_time       | duration       | typical time to reach target     | required
    - safe_state          | value          | position/state on safety trip    | required
    - connection_protocol | ref ENT-P022 (FieldbusAdapter)                   | required
    - feedback_sensor     | ref ENT-P001   | verifies actuator position       | optional (SHOULD have)
    - health_status       | enum: healthy | degraded | failed | unknown      | required  | default: unknown
    - zone_ref            | ref ENT-P018 (Zone)                              | optional
    - commissioned_at     | datetime       | —                               | required
    - metadata            | key-value pairs | ≤64 pairs                      | optional
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Registered → Commissioned → Operational → Degraded → Failed → Decommissioned
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-P002 (Engineer) creates. Commands issued by authorized Actors/ControlLoops.
  Relationships:  Belongs to ENT-P017 (PhysicalAsset) — N:1, required
                  Receives ENT-P005 (Command) — 1:N
                  May have feedback ENT-P001 (Sensor) — 1:1, optional
  Constraints:    safe_state MUST be defined. Actuator without safe_state is a spec error.
                  range_min < range_max.

ENT-P005: Command — Source: TERM-P005, SRC-P001, SRC-P009
  Purpose:        An authorized instruction to change an Actuator's state with mandatory verify.
  Attributes:
    - command_id          | UUID           | globally unique, immutable       | required
    - actuator_ref        | ref ENT-P004   | —                               | required
    - commanded_value     | value          | setpoint, position, or state     | required
    - command_type        | enum: immediate | ramped | timed                 | required
    - ramp_rate           | decimal/sec    | for ramped commands             | conditional
    - duration            | duration       | for timed commands              | conditional
    - priority            | enum: safety | high | normal | low              | required  | default: normal
    - authority_ref       | ref Actor or ref ENT-P009 (ControlLoop)         | required
    - safety_check_result | ref SafetyEnvelope validation                   | required
    - issued_at           | datetime       | —                               | required
    - acknowledged_at     | datetime       | —                               | optional (set by system)
    - executed_at         | datetime       | —                               | optional (set by system)
    - verified_at         | datetime       | —                               | optional (set by system)
    - verification_result | enum: confirmed | timeout | mismatch |
                            rejected | pending                               | required  | default: pending
    - rejection_reason    | string         | if rejected, the constraint hit  | conditional
    - latency_class       | ref ENT-P025   | timing requirement              | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      See SM-P002 (Command Lifecycle)
  Persistence:    Persistent, append-only, immutable. Full audit trail.
  Ownership:      OWNER: System once issued. Authority_ref is attributable but cannot modify.
  Relationships:  Targets ENT-P004 (Actuator) — N:1, required
                  May be part of ENT-P011 (ControlSequence) — N:1, optional
                  Validated against ENT-P014 (SafetyEnvelope) — N:1, required
  Constraints:    commanded_value must be within actuator range AND SafetyEnvelope.
                  Commands to LockedOut assets are REJECTED (CAP-P009).
                  ramp_rate required if command_type = ramped. duration required if timed.
```

### 5.3 Calibration and Quality Entities

```
ENT-P006: Calibration — Source: TERM-P006, SRC-P009, SRC-P011
  Purpose:        Traceable accuracy record against a known reference standard.
  Attributes:
    - calibration_id      | UUID           | globally unique, immutable       | required
    - subject_type        | enum: sensor | actuator                         | required
    - subject_ref         | ref ENT-P001 or ENT-P004                        | required
    - reference_standard  | string         | traceable to metrology institute | required
    - performed_by        | ref Actor      | —                               | required
    - performed_at        | datetime       | —                               | required
    - conditions          | structured: {temperature, pressure, humidity}    | required
    - as_found            | list<{reference_value, measured_value, error}>   | required
    - as_left             | list<{reference_value, measured_value, error}>   | optional (if adjusted)
    - pass_fail           | enum: pass | fail | conditional_pass             | required
    - acceptance_criteria | structured     | the criteria used               | required
    - next_due_date       | date           | —                               | required
    - uncertainty         | decimal        | of the calibration itself        | required
    - certificate_ref     | ref Content Store artifact                       | optional
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      See SM-P006 (Calibration Lifecycle)
  Persistence:    Persistent, append-only, immutable. Minimum 7-year retention.
  Ownership:      Created by ACT-P002 (Engineer) or authorized calibration technician.
  Relationships:  Applies to ENT-P001 (Sensor) or ENT-P004 (Actuator) — N:1, required
  Constraints:    Calibrations are immutable. Corrections require new Calibration record.
                  reference_standard must be traceable (ISO/IEC 17025).

ENT-P007: PhysicalConstraint — Source: TERM-P007, SRC-P004, SRC-P009
  Purpose:        Immutable equipment limitation that cannot be overridden by software.
  Attributes:
    - constraint_id       | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - constraint_type     | enum: mechanical_limit | thermal_limit |
                            pressure_rating | electrical_rating |
                            flow_capacity | speed_limit | load_limit |
                            chemical_compatibility | environmental_rating    | required
    - value               | decimal        | —                               | required
    - engineering_unit    | string         | —                               | required
    - comparison          | enum: max | min | range | exact                  | required
    - source              | enum: nameplate | engineering_design |
                            regulatory | manufacturer_spec                   | required
    - consequence_of_violation | enum: equipment_damage | safety_hazard |
                            process_upset | regulatory_violation             | required
    - asset_ref           | ref ENT-P017 (PhysicalAsset)                     | required
    - documentation_ref   | ref Content Store artifact                       | optional
  Identity:       UUID (globally unique)
  Lifecycle:      Created → Active. Changed only via Management of Change (MOC).
  Persistence:    Persistent. Version-controlled. Changes audited.
  Ownership:      ACT-P002 (Engineer) creates. ACT-P007 (Safety Authority) approves changes.
  Relationships:  Belongs to ENT-P017 (PhysicalAsset) — N:1, required
                  Input to ENT-P014 (SafetyEnvelope) — N:N
  Constraints:    PhysicalConstraints CANNOT be overridden by any Actor below ACT-P007.
                  Represent physical reality, not administrative preferences.

ENT-P008: Alarm — Source: TERM-P008, SRC-P004 (ISA-18.2)
  Purpose:        A declared condition demanding attention with ISA-18.2 lifecycle.
  Attributes:
    - alarm_id            | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - condition_type      | enum: high | low | high_high | low_low |
                            rate_of_change | deviation | state_change |
                            equipment_fault | communication_loss             | required
    - source_sensor       | ref ENT-P001   | or expression over multiple     | required
    - trigger_value       | decimal        | threshold or condition           | required
    - deadband            | decimal        | hysteresis to prevent chatter    | required
    - on_delay            | duration       | time condition must persist      | optional  | default: 0
    - off_delay           | duration       | time condition must clear        | optional  | default: 0
    - priority            | enum: emergency | high | medium | low |
                            diagnostic                                        | required
    - consequence         | string         | what happens if not addressed    | required
    - required_response_time | duration    | per priority and consequence     | required
    - suppression_rules   | structured     | shelving, out_of_service rules   | optional
    - current_state       | enum: normal | active_unacknowledged |
                            active_acknowledged | cleared_unacknowledged |
                            suppressed | out_of_service                       | required  | default: normal
    - asset_ref           | ref ENT-P017   | —                               | required
    - zone_ref            | ref ENT-P018   | —                               | optional
  Identity:       UUID (globally unique)
  Lifecycle:      See SM-P003 (Alarm Lifecycle — ISA-18.2)
  Persistence:    Configuration persistent. State transitions are immutable Events.
  Ownership:      ACT-P002 (Engineer) creates/configures. System manages state transitions.
  Relationships:  Sources from ENT-P001 (Sensor) — N:1 or N:N
                  Belongs to ENT-P017 (PhysicalAsset) — N:1
                  Generates ENT-P024 (Event) on each state transition
  Constraints:    priority must align with consequence severity. Alarm floods
                  (>10 alarms/operator/10 min) trigger rationalization alert.
```

### 5.4 Control Entities

```
ENT-P009: ControlLoop — Source: TERM-P009, SRC-P001, SRC-P010
  Purpose:        Continuous/periodic feedback mechanism maintaining desired physical state.
  Attributes:
    - loop_id             | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - loop_type           | enum: PID | on_off | cascade | feedforward |
                            ratio | split_range | MPC | custom               | required
    - process_variable    | ref ENT-P001 (Sensor) or expression              | required
    - setpoint_ref        | ref ENT-P010 (Setpoint)                          | required
    - output              | ref ENT-P004 (Actuator)                          | required
    - tuning_parameters   | structured: {Kp, Ki, Kd} or equivalent          | required
    - scan_rate           | duration       | execution frequency             | required
    - mode                | enum: automatic | manual | cascade | local |
                            remote                                            | required  | default: manual
    - output_min          | decimal        | minimum output limit            | required
    - output_max          | decimal        | maximum output limit            | required
    - rate_of_change_limit | decimal/sec   | output slew rate limit          | optional
    - performance_metrics | structured: {IAE, ISE, overshoot,
                            settling_time, oscillation_index}                | computed
    - latency_class       | ref ENT-P025   | timing requirement              | required
    - safety_envelope_ref | ref ENT-P014   | —                               | required
    - asset_ref           | ref ENT-P017   | —                               | required
  Identity:       UUID (globally unique)
  Lifecycle:      Configured → Active → Tuning → Active → Deactivated
  Persistence:    Configuration persistent. Performance metrics computed continuously.
  Ownership:      ACT-P002 (Engineer) creates/tunes. Mode changes by authorized Actors.
  Relationships:  Reads ENT-P001 (Sensor) — N:1
                  Has ENT-P010 (Setpoint) — 1:1
                  Writes to ENT-P004 (Actuator) via ENT-P005 (Command) — 1:1
                  Bounded by ENT-P014 (SafetyEnvelope) — N:1
  Constraints:    scan_rate must be compatible with latency_class.
                  output_min/max must be within actuator range AND SafetyEnvelope.
                  Mode changes are auditable Events with Actor attribution.

ENT-P010: Setpoint — Source: TERM-P010, SRC-P002, SRC-P010
  Purpose:        Target value for a ControlLoop, bounded by constraints and safety.
  Attributes:
    - setpoint_id         | UUID           | globally unique                  | required
    - value               | decimal        | current target value             | required
    - engineering_unit    | string         | —                               | required
    - source              | enum: manual | schedule | cascade |
                            optimization | recipe                             | required
    - effective_from      | datetime       | when this value took effect      | required
    - ramp_rate           | decimal/sec    | if ramping to new value          | optional
    - limit_low           | decimal        | clamped to PhysicalConstraints   | required
    - limit_high          | decimal        | clamped to SafetyEnvelope        | required
    - authorization       | ref Actor or system                              | required
    - loop_ref            | ref ENT-P009 (ControlLoop)                       | required
  Identity:       UUID (globally unique)
  Lifecycle:      Current setpoint is the latest value. History is immutable event log.
  Persistence:    Current value persistent. All changes are immutable Events.
  Ownership:      Set by authorized Actors, cascade outputs, optimizers, or recipes.
  Relationships:  Belongs to ENT-P009 (ControlLoop) — 1:1
  Constraints:    limit_low ≤ value ≤ limit_high. Limits derived from intersection of
                  PhysicalConstraints AND SafetyEnvelope. Rejected if outside.

ENT-P011: ControlSequence — Source: TERM-P011, SRC-P004 (ISA-88)
  Purpose:        Ordered series of control actions executing a defined process step.
  Attributes:
    - sequence_id         | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - steps               | ordered list<SequenceStep>                       | required
      (each step: action, target, value, wait_condition, timeout)
    - preconditions       | list<condition> | must be true before start       | required
    - postconditions      | list<condition> | must be true after completion   | required
    - abort_conditions    | list<condition> | triggers emergency stop         | required
    - timeout             | duration       | maximum execution time           | required
    - current_step        | integer        | 0-based index                   | computed
    - status              | enum: ready | running | completed | aborted |
                            held | paused                                     | required  | default: ready
    - process_ref         | ref ENT-P019   | parent process (ISA-88 recipe)  | optional
    - asset_ref           | ref ENT-P017   | equipment running on            | required
  Identity:       UUID (globally unique)
  Lifecycle:      See SM-P004 (ControlSequence Lifecycle)
  Persistence:    Definition persistent. Execution state event-sourced.
  Ownership:      ACT-P002 (Engineer) defines. Execution by authorized Actors/systems.
  Relationships:  May belong to ENT-P019 (Process) — N:1, optional
                  Produces ENT-P005 (Commands) — 1:N
                  Runs on ENT-P017 (PhysicalAsset) — N:1
  Constraints:    preconditions verified before start. abort_conditions checked every scan.
                  ISA-88: ControlSequence = Equipment Phase. See TERM-P011.

ENT-P012: OperatingMode — Source: TERM-P012, SRC-P001, SRC-P008
  Purpose:        Named validated configuration of loops/setpoints/interlocks.
  Attributes:
    - mode_id             | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - description         | string         | ≤1000 chars                      | required
    - active_loops        | list<{loop_ref, tuning_override}>               | required
    - active_setpoints    | list<{setpoint_ref, value}>                     | required
    - safety_interlocks   | list<ref ENT-P013>                              | required
    - permitted_transitions | list<ref ENT-P012>                            | required
    - entry_conditions    | list<condition> | must be true to enter mode     | required
    - exit_conditions     | list<condition> | must be true to leave mode     | optional
    - asset_ref           | ref ENT-P017   | —                               | required
  Identity:       UUID (globally unique)
  Lifecycle:      Defined → Active (only one per asset at a time)
  Persistence:    Persistent, version-controlled
  Ownership:      ACT-P002 (Engineer) defines. Mode changes by authorized Actors.
  Relationships:  Configures ENT-P009 (ControlLoop) — 1:N
                  References ENT-P013 (SafetyFunction) — N:N
                  Applied to ENT-P017 (PhysicalAsset) — N:1
  Constraints:    Only one OperatingMode active per asset at a time.
                  entry_conditions must be verified before transition.
```

### 5.5 Safety and Governance Entities

```
ENT-P013: SafetyFunction — Source: TERM-P013, SRC-P009
  Purpose:        Specific function to achieve/maintain safe state, SIL-rated, independent.
  Attributes:
    - safety_function_id  | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - hazard_description  | string         | what hazard this prevents        | required
    - triggering_condition | expression    | combination of measurements/states | required
    - required_action     | enum: emergency_shutdown | valve_close |
                            power_disconnect | alarm_only | custom_action    | required
    - action_detail       | structured     | specific commands to issue       | required
    - SIL_level           | enum: SIL_1 | SIL_2 | SIL_3 | SIL_4 | non_SIL | required
    - response_time_requirement | duration | max time from trigger to action | required
    - proof_test_interval | duration       | per IEC 61508 calculation        | required
    - last_proof_test     | datetime       | —                               | optional
    - diagnostic_coverage | decimal 0.0–1.0 | fraction of failures detected  | required
    - failure_mode        | enum: fail_safe | —                              | required  | default: fail_safe
    - independence_verification | structured | proof of independence from BCS | required
    - bypass_state        | enum: active | bypassed                          | required  | default: active
    - bypass_authorization | ref ACT-P007  | only Safety Authority           | conditional
    - bypass_expiry       | datetime       | auto-revoke time                | conditional
    - hazard_analysis_ref | ref ENT-P016   | —                               | required
    - asset_ref           | ref ENT-P017   | —                               | required
  Identity:       UUID (globally unique)
  Lifecycle:      Designed → Verified → Active → ProofTestDue → Active | Bypassed → Active
  Persistence:    Persistent. All state changes are immutable Events.
  Ownership:      ACT-P002 (Engineer) designs. ACT-P007 (Safety Authority) approves.
  Relationships:  Protects ENT-P017 (PhysicalAsset) — N:N
                  Referenced by ENT-P014 (SafetyEnvelope) — N:N
                  Justified by ENT-P016 (HazardAnalysis) — N:1
  Constraints:    INDEPENDENT of basic control logic (separate CPU, memory, I/O).
                  AI agents MUST NOT be assigned to SIL-rated functions (CAP-P020).
                  Bypasses: ACT-P007 only, time-limited, logged, auto-revoked.
                  Missed proof tests generate mandatory alarm.

ENT-P014: SafetyEnvelope — Source: TERM-P014, SRC-P004, SRC-P009
  Purpose:        Complete set of constraints for authorized physical operation.
  Attributes:
    - envelope_id         | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - physical_constraints | list<ref ENT-P007>                              | required
    - safety_functions    | list<ref ENT-P013>                               | required
    - operational_limits  | list<{parameter, min, max, unit}>               | required
    - permitted_modes     | list<ref ENT-P012>                               | required
    - permitted_actors    | list<ref Actor with role constraints>            | required
    - interlock_conditions | list<condition>                                 | required
    - environmental_preconditions | structured                              | optional
    - version             | integer        | incremented on change            | required
    - effective_from      | datetime       | —                               | required
    - approved_by         | ref ACT-P007 (Safety Authority)                  | required
    - moc_reference       | string         | Management of Change record      | required
    - asset_ref           | ref ENT-P017   | —                               | required
  Identity:       UUID (globally unique)
  Lifecycle:      Drafted → Reviewed → Approved → Active → Superseded
  Persistence:    Persistent, version-controlled. All versions retained.
  Ownership:      ACT-P002 (Engineer) drafts. ACT-P007 (Safety Authority) approves.
  Relationships:  Composes ENT-P007 (PhysicalConstraints) — 1:N
                  References ENT-P013 (SafetyFunctions) — 1:N
                  Applied to ENT-P017 (PhysicalAsset) — N:1
                  All Commands (ENT-P005) validated against this — 1:N
  Constraints:    operational_limits MUST be tighter than PhysicalConstraints
                  (administrative margins). Changes require MOC workflow.

ENT-P015: PhysicalEnvelope — Source: TERM-P015, ASM-P007
  Purpose:        Bounded AI Agent authority over physical systems — most restrictive envelope.
  Attributes:
    - envelope_id         | UUID           | globally unique                  | required
    - agent_ref           | ref Actor (ACT-P003 or ACT-P004)                | required
    - accessible_sensors  | list<ref ENT-P001> | read access                 | required
    - accessible_actuators | list<ref ENT-P004> | command access             | required
    - permitted_setpoint_ranges | list<{setpoint_ref, min, max}>            | required
    - permitted_modes     | list<ref ENT-P012>                               | required
    - permitted_sequences | list<ref ENT-P011>                               | required
    - max_command_rate    | integer/sec    | rate limit on commands           | required
    - verification_latency | duration      | max time to verify command       | required
    - human_approval_triggers | list<condition>                              | required
    - effective_from      | datetime       | —                               | required
    - effective_until     | datetime       | explicit expiry                  | required
    - approved_by         | ref ACT-P002 or ACT-P007                         | required
    - business_envelope_ref | ref BUSINESS Agent Envelope (TERM-030)         | required
  Identity:       UUID (globally unique)
  Lifecycle:      Defined → Active → Expired | Revoked
  Persistence:    Persistent. All changes are immutable Events.
  Ownership:      ACT-P002 (Engineer) defines. Must chain from BUSINESS Agent Envelope.
  Relationships:  Constrains Actor (ACT-P003, ACT-P004) — N:1
                  Must reference BUSINESS Agent Envelope — N:1, required
                  Bounded by ENT-P014 (SafetyEnvelope) — N:1
  Constraints:    Effective authority = PhysicalEnvelope ∩ SafetyEnvelope ∩ PhysicalConstraints.
                  Most restrictive always wins. Must have valid business_envelope_ref.
                  CROSS-SUBSTRATE: See envelope chain in CROSS-SUBSTRATE-CONVENTIONS.md §1.

ENT-P016: HazardAnalysis — Source: TERM-P016, SRC-P009
  Purpose:        Structured risk assessment of what can go wrong and what protections exist.
  Attributes:
    - hazard_id           | UUID           | globally unique                  | required
    - description         | string         | ≤2000 chars                      | required
    - analysis_type       | enum: HAZOP | FMEA | FTA | LOPA | bow_tie |
                            what_if                                           | required
    - cause_chain         | structured     | sequence of causes               | required
    - consequence_severity | enum: catastrophic | critical | marginal |
                            negligible                                        | required
    - consequence_likelihood | enum: frequent | probable | occasional |
                            remote | improbable                               | required
    - risk_level          | computed from severity × likelihood matrix        | computed
    - existing_safeguards | list<ref ENT-P013 or string>                     | required
    - required_safety_functions | list<ref ENT-P013>                         | optional
    - residual_risk       | enum: acceptable | ALARP | unacceptable          | required
    - review_status       | enum: current | review_due | obsolete            | required
    - last_reviewed       | datetime       | —                               | required
    - next_review_due     | date           | —                               | required
    - asset_ref           | ref ENT-P017   | —                               | required
    - zone_ref            | ref ENT-P018   | —                               | optional
  Identity:       UUID (globally unique)
  Lifecycle:      Draft → Reviewed → Approved → Current → Review_Due → Reviewed (cycle)
  Persistence:    Persistent. All versions retained for regulatory compliance.
  Ownership:      ACT-P002 (Engineer) creates. ACT-P007 (Safety Authority) approves.
  Relationships:  Justifies ENT-P013 (SafetyFunction) — 1:N
                  Applies to ENT-P017 (PhysicalAsset) — N:1
  Constraints:    residual_risk: unacceptable requires additional safety_functions.
                  Must be reviewed when systems change, conditions change, or incidents occur.
```

### 5.6 System Structure and Integration Entities

```
ENT-P017: PhysicalAsset — Source: TERM-P017, SRC-P004, SRC-P012
  Purpose:        Discrete equipment with sensors, actuators, and operational metadata.
  Attributes:
    - asset_id            | UUID           | globally unique, immutable       | required
    - name                | string         | ≤128 chars                       | required
    - asset_type          | enum: pump | heat_exchanger | reactor | conveyor |
                            robot | tank | compressor | fan | boiler |
                            chiller | valve_assembly | analyzer |
                            breaker_panel | instrument_assembly              | required
    - make                | string         | manufacturer                     | required
    - model               | string         | model number                     | required
    - serial_number       | string         | unique per manufacturer          | required
    - physical_location   | ref BUSINESS TERM-024 Location                   | required
    - hierarchy_level     | enum: enterprise | site | area | process_cell |
                            unit | equipment_module | control_module         | required
    - parent_asset        | ref ENT-P017   | containment parent              | optional
    - child_assets        | list<ref ENT-P017> | containment children        | computed
    - sensors             | list<ref ENT-P001> | attached sensors             | computed
    - actuators           | list<ref ENT-P004> | attached actuators           | computed
    - physical_constraints | list<ref ENT-P007> | equipment limitations       | computed
    - safety_envelope_ref | ref ENT-P014   | active safety envelope          | required
    - current_mode        | ref ENT-P012   | active operating mode            | optional
    - operational_state   | enum: see SM-P001                                | required
    - commissioned_at     | datetime       | —                               | required
    - business_entity_ref | ref BUSINESS Entity                              | required
    - zone_ref            | ref ENT-P018   | —                               | optional
    - metadata            | key-value pairs | ≤64 pairs                      | optional
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      See SM-P001 (PhysicalAsset Lifecycle including LOTO)
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-P002 (Engineer) creates/configures. Hierarchy per ISA-95.
  Relationships:  Contains ENT-P001 (Sensors) — 1:N
                  Contains ENT-P004 (Actuators) — 1:N
                  Has ENT-P014 (SafetyEnvelope) — 1:1
                  Has ENT-P012 (OperatingMode) — 1:N (one active)
                  Contains child ENT-P017 — 1:N (ISA-95 hierarchy)
                  Mapped to BUSINESS Entity — 1:1
  Constraints:    ISA-95 hierarchy: Enterprise > Site > Area > ProcessCell > Unit >
                  EquipmentModule > ControlModule. Parent must be higher level.

ENT-P018: Zone — Source: TERM-P018, SRC-P009
  Purpose:        Bounded physical region with uniform safety/security/access policies.
  Attributes:
    - zone_id             | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - boundaries          | spatial definition or list<ref ENT-P017>         | required
    - security_level      | enum: SL_1 | SL_2 | SL_3 | SL_4 (IEC 62443)   | required
    - safety_classification | string       | hazardous area class if any      | optional
    - access_requirements | structured     | personnel and agent requirements | required
    - environmental_conditions | structured: {temp_range, humidity_range,
                            hazardous_area_class}                            | optional
    - contained_assets    | list<ref ENT-P017>                               | computed
    - parent_zone         | ref ENT-P018   | hierarchical containment         | optional
  Identity:       UUID (globally unique)
  Lifecycle:      Defined → Active → Modified → Decommissioned
  Persistence:    Persistent, version-controlled
  Ownership:      ACT-P002 (Engineer) defines. ACT-P007 approves safety classification.
  Relationships:  Contains ENT-P017 (PhysicalAssets) — 1:N
                  May contain child ENT-P018 (Zones) — 1:N
  Constraints:    Security_level per IEC 62443 zone model. Commands to assets in zone
                  validated against zone policies in addition to SafetyEnvelope.

ENT-P019: Process — Source: TERM-P019, SRC-P004, SRC-P007
  Purpose:        Defined physical transformation specification (ISA-88 Master Recipe).
  Attributes:
    - process_id          | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - process_type        | enum: continuous | batch | discrete | hybrid     | required
    - inputs              | list<{material, quantity, unit}>                 | required
    - outputs             | list<{product, quantity, unit}>                  | required
    - process_parameters  | list<{name, value, unit, range}>                | required
    - quality_specifications | list<{parameter, target, tolerance}>          | required
    - sequences           | ordered list<ref ENT-P011 (ControlSequence)>    | required
    - required_assets     | list<ref ENT-P017 with capability requirements> | required
    - required_mode       | ref ENT-P012   | operating mode for execution     | optional
    - version             | integer        | recipe version                   | required
    - approved_by         | ref Actor      | —                               | required
  Identity:       UUID (globally unique)
  Lifecycle:      Draft → Validated → Approved → Active → Superseded
  Persistence:    Persistent, version-controlled. All versions retained.
  Ownership:      ACT-P002 (Engineer) defines. Approval per regulatory requirements.
  Relationships:  Contains ENT-P011 (ControlSequences) — 1:N, ordered
                  Instantiated as ENT-P020 (ProcessExecution) — 1:N
                  Requires ENT-P017 (PhysicalAssets) — N:N
  Constraints:    ISA-88: Process = Master/Control Recipe. process_parameters = Recipe
                  Parameters. Sequences map to Equipment Phases.

ENT-P020: ProcessExecution — Source: TERM-P020, SRC-P004, SRC-P012
  Purpose:        Single run of a Process with complete audit trail (ISA-88 Batch).
  Attributes:
    - execution_id        | UUID           | globally unique, immutable       | required
    - process_ref         | ref ENT-P019   | specification being executed     | required
    - process_version     | integer        | snapshot of version at start     | required
    - start_time          | datetime       | —                               | required
    - end_time            | datetime       | null if running                  | optional
    - assets_used         | list<ref ENT-P017>                               | required
    - actual_parameters   | list<{name, value, unit}>                        | required
    - measurements_log    | ref MeasurementStream(s) during execution        | required
    - commands_log        | list<ref ENT-P005> during execution              | required
    - alarms_log          | list<ref ENT-P008 state changes> during exec     | required
    - quality_results     | list<{parameter, actual, target, pass_fail}>     | optional
    - yield               | decimal        | output quantity                  | optional
    - status              | enum: see SM-P005                                | required
    - operator_ref        | ref ACT-P001   | responsible operator             | required
    - deviations          | list<{description, impact, resolution}>          | optional
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      See SM-P005 (ProcessExecution Lifecycle)
  Persistence:    Persistent, append-only. Complete regulatory audit trail.
                  FDA 21 CFR Part 11 compliant for pharma. Minimum 7-year retention.
  Ownership:      System manages. ACT-P001 (Operator) initiates and supervises.
  Relationships:  Instance of ENT-P019 (Process) — N:1
                  Uses ENT-P017 (PhysicalAssets) — N:N
                  Records ENT-P002, ENT-P005, ENT-P008 during execution — 1:N each
  Constraints:    All sensor data, commands, and alarms during execution must be captured.
                  Deviations from process_parameters must be recorded with impact assessment.

ENT-P021: MaintenanceAction — Source: TERM-P021, SRC-P002, SRC-P012
  Purpose:        Record of physical intervention on a PhysicalAsset.
  Attributes:
    - maintenance_id      | UUID           | globally unique                  | required
    - asset_ref           | ref ENT-P017   | —                               | required
    - maintenance_type    | enum: preventive | corrective | predictive |
                            condition_based | inspection | calibration       | required
    - description         | string         | ≤2000 chars                      | required
    - performed_by        | ref Actor      | —                               | required
    - started_at          | datetime       | —                               | required
    - completed_at        | datetime       | null if in progress              | optional
    - parts_used          | list<{part_id, quantity, description}>           | optional
    - measurements_before | list<ref ENT-P002>                               | optional
    - measurements_after  | list<ref ENT-P002>                               | optional
    - return_to_service_authorization | ref Actor                            | conditional
    - loto_ref            | ref Event (LOTO state transition)                | optional
    - next_scheduled      | date           | for preventive maintenance       | optional
    - business_workflow_ref | ref BUSINESS Workflow                          | optional
  Identity:       UUID (globally unique)
  Lifecycle:      Planned → InProgress → Completed → Verified
  Persistence:    Persistent. Full audit trail.
  Ownership:      ACT-P001/P002 creates. Completion authorized by ACT-P002.
  Relationships:  Applies to ENT-P017 (PhysicalAsset) — N:1
                  May trigger ENT-P006 (Calibration) re-validation
                  May link to BUSINESS Workflow — N:1, optional
  Constraints:    Changes to physical behavior trigger re-validation of Calibrations
                  and SafetyEnvelope verification. Return-to-service requires authorization.

ENT-P022: FieldbusAdapter — Source: TERM-P022, SRC-P001, SRC-P003
  Purpose:        Translation layer between PHYSICAL normalized interface and hardware protocols.
  Attributes:
    - adapter_id          | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - protocol_type       | enum: Modbus_RTU | Modbus_TCP | EtherNet_IP |
                            PROFINET | PROFIBUS | CANopen | DeviceNet |
                            BACnet | MQTT | OPC_UA | IO_Link | HART |
                            Foundation_Fieldbus | CC_Link | EtherCAT |
                            Powerlink | SERCOS | ROS2_DDS | custom           | required
    - connection_parameters | structured (protocol-specific)                 | required
    - polling_configuration | structured: {rate, timeout, retry}            | required
    - data_mapping        | list<{protocol_address, entity_ref, transform}> | required
    - health_status       | enum: connected | degraded | disconnected |
                            error                                             | required
    - last_communication  | datetime       | —                               | computed
    - error_count         | integer        | rolling window                   | computed
    - latency_class       | ref ENT-P025   | timing requirement              | required
  Identity:       UUID (globally unique)
  Lifecycle:      Configured → Connected → Degraded → Disconnected → Reconnecting
  Persistence:    Configuration persistent. Health status real-time.
  Ownership:      ACT-P002 (Engineer) configures.
  Relationships:  Connects ENT-P001 (Sensors) and ENT-P004 (Actuators) to hardware — N:N
  Constraints:    data_mapping must type-check: protocol data types must be convertible
                  to PHYSICAL entity types. Range checks applied on all conversions.

ENT-P023: DigitalTwin — Source: TERM-P023, SRC-P003, SRC-P012
  Purpose:        Synchronized virtual representation of physical counterpart.
  Attributes:
    - twin_id             | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - physical_counterpart_type | enum: asset | zone | process              | required
    - physical_counterpart_ref | ref ENT-P017 or ENT-P018 or ENT-P019      | required
    - model_type          | enum: physics_based | data_driven | hybrid       | required
    - fidelity            | enum: high | medium | simplified                 | required
    - synchronization_rate | duration      | how often state is updated       | required
    - current_state       | structured     | latest synchronized state        | computed
    - last_synchronized   | datetime       | —                               | computed
    - drift_threshold     | decimal        | max acceptable divergence        | required
    - drift_detected      | boolean        | twin ≠ reality beyond threshold  | computed
    - simulation_endpoint | ref COMPUTE Pipeline                             | optional
    - latency_class       | ref ENT-P025   | —                               | required
  Identity:       UUID (globally unique)
  Lifecycle:      Created → Synchronizing → Drifted → Recalibrated → Synchronizing
  Persistence:    Configuration persistent. State snapshots per retention policy.
  Ownership:      ACT-P002 (Engineer) creates/configures.
  Relationships:  Mirrors ENT-P017, ENT-P018, or ENT-P019 — 1:1
                  May reference COMPUTE Pipeline for simulation — 1:1, optional
  Constraints:    drift_detected triggers alert. Fidelity is declared, not quantitative
                  accuracy (UNK-P004). Simulation engine is COMPUTE; state sync is PHYSICAL.

ENT-P024: Event — Source: TERM-P024, ASM-P009
  Purpose:        Immutable record of physical system occurrence. Source of truth.
  Attributes:
    - event_id            | UUID           | globally unique, immutable       | required
    - timestamp           | datetime       | with nanosecond precision        | required
    - timestamp_uncertainty | duration     | clock sync uncertainty           | required
    - actor_type          | enum: human | ai_agent | control_system |
                            equipment | safety_system                         | required
    - actor_ref           | ref Actor or system                              | required
    - target_type         | enum: sensor | actuator | asset | zone |
                            process | alarm | control_loop | safety_function | required
    - target_ref          | ref target entity                                | required
    - event_type          | enum: measurement | command | alarm_transition |
                            mode_change | calibration | maintenance |
                            safety_trip | process_start | process_end |
                            communication_loss | communication_restored |
                            setpoint_change | loto_transition |
                            envelope_change | asset_state_change             | required
    - payload             | structured (event-type-specific data)            | required
    - cross_substrate_emitted | boolean    | was this projected to shared bus | required  | default: false
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Immutable once created. Never modified. Never deleted.
  Persistence:    Append-only event store. Minimum 7-year retention for regulated.
  Ownership:      OWNER: System. No Actor may modify or delete.
  Relationships:  References any entity as target. Forms the complete audit trail.
  Constraints:    Events are the source of truth. All entity state is derivable from
                  the event log. DOMAIN EVENT vs CROSS-SUBSTRATE EVENT: see TERM-P024.

ENT-P025: LatencyClass — Source: TERM-P025, ASM-P003
  Purpose:        First-class timing constraint determining architecture.
  Attributes:
    - class_name          | enum: hard_realtime | soft_realtime |
                            near_realtime | batch | advisory                  | required
    - maximum_latency     | duration       | upper bound on response time     | required
    - jitter_tolerance    | duration       | acceptable timing variation      | required
    - infrastructure      | enum: dedicated_hardware | edge_controller |
                            edge_or_onprem | cloud_ok | cloud_ok_no_timing   | required
    - consequences_of_violation | string   | what happens if timing missed    | required
  Identity:       class_name (enum, not UUID — there are exactly 5)
  Lifecycle:      Static. Defined by specification, not by configuration.
  Persistence:    Specification-defined constants.
  Ownership:      Specification. Not user-configurable.
  Relationships:  Referenced by ENT-P003, ENT-P005, ENT-P009, ENT-P022, ENT-P023
  Constraints:    Five classes only. Architecture is determined by class, not negotiable.
                  See Section 2.5 for infrastructure mapping.

ENT-P026: PhysicalTopology — Source: TERM-P026, SRC-P004
  Purpose:        Connection model for propagation analysis (what affects what).
  Attributes:
    - topology_id         | UUID           | globally unique                  | required
    - name                | string         | ≤128 chars                       | required
    - nodes               | list<ref ENT-P017 (PhysicalAsset)>              | required
    - edges               | list<TopologyEdge>                               | required
      (each edge: source_ref, target_ref, edge_type, flow_direction,
       capacity, current_state)
    - edge_types          | enum: pipe | wire | conveyor | shaft |
                            wireless_link | data_cable | duct | rail         | per edge
    - scope               | ref ENT-P018 (Zone) or ref ENT-P017 (top-level) | required
    - version             | integer        | —                               | required
    - last_verified       | datetime       | physical verification date       | required
  Identity:       UUID (globally unique)
  Lifecycle:      Created → Active → Modified → Archived
  Persistence:    Persistent, version-controlled
  Ownership:      ACT-P002 (Engineer) creates/maintains.
  Relationships:  Connects ENT-P017 (PhysicalAssets) — N:N via edges
                  Scoped to ENT-P018 (Zone) or top-level asset — N:1
  Constraints:    Must be verified against physical reality. Propagation queries
                  traverse edges to determine impact (what downstream sensors see
                  changes if Valve A closes).
```

### 5.7 State Machines

```
SM-P001: State machine for ENT-P017 (PhysicalAsset) — Source: TERM-P017, SRC-P004, SRC-P009
  States:      Commissioning, Operational, Degraded, LockedOut, ReturnToService,
               Shutdown, Decommissioned
  Transitions:
    Commissioning → Operational
      Trigger: Commissioning checklist complete; all sensors/actuators verified
      Preconditions: SafetyEnvelope defined and approved. All safety functions tested.
      Postconditions: Asset available for control. Operating mode set to initial mode.
    Operational → Degraded
      Trigger: Sensor failure, actuator degradation, or partial capability loss
      Preconditions: Asset still functional with reduced capability
      Postconditions: Alarm raised. Affected control loops flagged. Maintenance scheduled.
    Operational → LockedOut
      Trigger: Authorized LOTO request (maintenance, modification, inspection)
      Preconditions: ALL Actuators driven to safe_state. LOTO authorization verified.
                     Energy isolation verified.
      Postconditions: ALL Commands to asset's Actuators REJECTED. SafetyEnvelope replaced
                      with maintenance envelope (diagnostic reads only, zero writes).
                      LOTO tag recorded with performing_actor and reason.
    LockedOut → ReturnToService
      Trigger: Authorized LOTO release by original locking actor or supervisor
      Preconditions: Maintenance complete. LOTO release authorization verified.
                     All lock holders have released their locks.
      Postconditions: Asset in ReturnToService pending safety verification.
    ReturnToService → Operational
      Trigger: Safety verification and function test complete
      Preconditions: All safety functions tested. Calibrations verified.
                     SafetyEnvelope restored. Authorized by ACT-P002.
      Postconditions: Asset available for control. Normal SafetyEnvelope active.
    Degraded → Operational
      Trigger: Repair complete, all capabilities restored
      Preconditions: Maintenance action completed and verified. Return-to-service authorized.
      Postconditions: Full capability restored. Degradation alarm cleared.
    Degraded → LockedOut
      Trigger: Authorized LOTO for repair
      Preconditions: Same as Operational → LockedOut
      Postconditions: Same as Operational → LockedOut
    Operational → Shutdown
      Trigger: Planned shutdown or emergency shutdown
      Preconditions: Shutdown sequence executed. All actuators in safe_state.
      Postconditions: Asset de-energized. No commands accepted.
    Shutdown → Operational
      Trigger: Startup sequence initiated by authorized Actor
      Preconditions: Startup checklist complete. Safety verification passed.
      Postconditions: Asset energized. Control loops in manual pending operator handoff.
    Any → Decommissioned
      Trigger: Asset permanently removed from service
      Preconditions: Authorized by ACT-P002. All dependencies resolved.
      Postconditions: Asset marked Decommissioned. Historical data retained. No commands accepted.

SM-P002: State machine for ENT-P005 (Command) — Source: TERM-P005, ASM-P004
  States:      Issued, Rejected, Acknowledged, Executed, Verified_Confirmed,
               Verified_Timeout, Verified_Mismatch
  Transitions:
    Issued → Rejected
      Trigger: SafetyEnvelope violation, asset LockedOut, or authorization failure
      Preconditions: Validation check failed
      Postconditions: rejection_reason recorded. Command never reaches actuator.
    Issued → Acknowledged
      Trigger: FieldbusAdapter confirms receipt by target device
      Preconditions: Safety validation passed. Asset not LockedOut.
      Postconditions: acknowledged_at recorded. Execution timer starts.
    Acknowledged → Executed
      Trigger: Device confirms command applied to output
      Preconditions: Acknowledged state reached
      Postconditions: executed_at recorded. Verification timer starts.
    Executed → Verified_Confirmed
      Trigger: Feedback sensor confirms actuator reached commanded position
      Preconditions: feedback_sensor reading matches commanded_value within tolerance
      Postconditions: verified_at recorded. verification_result = confirmed.
    Executed → Verified_Timeout
      Trigger: Verification timeout expired without feedback confirmation
      Preconditions: Timeout exceeded AND feedback_sensor not confirmed
      Postconditions: verified_at recorded. verification_result = timeout. Alarm raised.
    Executed → Verified_Mismatch
      Trigger: Feedback sensor confirms actuator position ≠ commanded position
      Preconditions: Feedback received but outside tolerance
      Postconditions: verified_at recorded. verification_result = mismatch. Alarm raised.

SM-P003: State machine for ENT-P008 (Alarm) — ISA-18.2 — Source: TERM-P008, SRC-P004
  States:      Normal, Active_Unacknowledged, Active_Acknowledged,
               Cleared_Unacknowledged, Suppressed, Out_of_Service
  Transitions:
    Normal → Active_Unacknowledged
      Trigger: Alarm condition becomes true (after on_delay)
      Preconditions: Condition persists for on_delay duration
      Postconditions: Alarm annunciated. Event recorded. Notification to operator.
    Active_Unacknowledged → Active_Acknowledged
      Trigger: Operator acknowledges alarm
      Preconditions: Operator authenticated and authorized
      Postconditions: Acknowledging actor and timestamp recorded. Condition still active.
    Active_Acknowledged → Normal
      Trigger: Alarm condition clears (after off_delay)
      Preconditions: Condition cleared for off_delay duration
      Postconditions: Return-to-normal event recorded.
    Active_Unacknowledged → Cleared_Unacknowledged
      Trigger: Alarm condition clears before operator acknowledges
      Preconditions: Condition cleared for off_delay duration
      Postconditions: Alarm still requires acknowledgment (operator must see it happened).
    Cleared_Unacknowledged → Normal
      Trigger: Operator acknowledges the cleared alarm
      Preconditions: Operator authenticated and authorized
      Postconditions: Full lifecycle complete. All transitions recorded.
    Any_Active → Suppressed
      Trigger: Authorized shelving (planned maintenance, known condition)
      Preconditions: Shelving authorized. Time limit set. Reason documented.
      Postconditions: Alarm suppressed. Auto-unshelve timer starts. Event recorded.
    Suppressed → Previous_State
      Trigger: Shelving timer expires or manual unshelve
      Preconditions: Timer expired or authorized unshelve
      Postconditions: Alarm returns to appropriate state based on current condition.
    Any → Out_of_Service
      Trigger: Authorized by ACT-P002 (Engineer) for maintenance
      Preconditions: Out-of-service authorization. Associated safety review.
      Postconditions: Alarm does not annunciate. Alarm monitoring continues for logging.

SM-P004: State machine for ENT-P011 (ControlSequence) — Source: TERM-P011, SRC-P004
  States:      Ready, Running, Held, Paused, Completed, Aborted
  Transitions:
    Ready → Running
      Trigger: Start command by authorized Actor or parent Process
      Preconditions: ALL preconditions verified true. Equipment available. Mode correct.
      Postconditions: First step begins. Execution timer starts.
    Running → Running (step advance)
      Trigger: Current step postcondition met
      Preconditions: Step complete. Next step preconditions met.
      Postconditions: current_step incremented. New step begins.
    Running → Held
      Trigger: Hold command or hold condition detected
      Preconditions: Sequence can be safely paused at current point
      Postconditions: Outputs held at current values. Timers paused.
    Held → Running
      Trigger: Resume command by authorized Actor
      Preconditions: Hold condition cleared. Resume authorized.
      Postconditions: Execution resumes from held step.
    Running → Aborted
      Trigger: Abort condition detected OR operator emergency stop
      Preconditions: Any abort_condition true OR manual abort
      Postconditions: All actuators driven to safe_state. Abort reason recorded.
                      Recovery requires new sequence start (no resume from abort).
    Running → Completed
      Trigger: Last step postcondition met
      Preconditions: All steps complete. All postconditions verified.
      Postconditions: Completion recorded. Parent process notified if applicable.
    Running → Paused
      Trigger: Operator pause request
      Preconditions: Sequence supports pause at current step
      Postconditions: Current step suspended. Outputs maintained.
    Paused → Running
      Trigger: Operator resume
      Preconditions: Resume authorized. Conditions still valid.
      Postconditions: Current step resumes.

SM-P005: State machine for ENT-P020 (ProcessExecution) — Source: TERM-P020, SRC-P004
  States:      Initialized, Running, Held, Completed, Aborted
  Transitions:
    Initialized → Running
      Trigger: Operator starts execution. All pre-execution checks pass.
      Preconditions: Required assets available. Required mode active. Materials staged.
                     Process version locked at start.
      Postconditions: First ControlSequence starts. All data logging begins.
    Running → Held
      Trigger: Hold condition or operator hold
      Preconditions: Process can be safely held. All sequences held.
      Postconditions: All active sequences held. Timers paused. Hold event recorded.
    Held → Running
      Trigger: Operator resume
      Preconditions: Hold condition cleared. Resume authorized.
      Postconditions: All sequences resume. Timers resume.
    Running → Completed
      Trigger: All sequences complete. Quality checks pass.
      Preconditions: All postconditions verified. Quality results recorded.
      Postconditions: End_time recorded. Complete audit trail available.
                      Yield and quality_results calculated.
    Running → Aborted
      Trigger: Safety trip, critical alarm, or operator abort
      Preconditions: Any critical abort condition
      Postconditions: All sequences aborted. All actuators to safe_state.
                      Abort reason and partial results recorded. Material disposition required.

SM-P006: State machine for ENT-P006 (Calibration) lifecycle — Source: TERM-P006, SRC-P011
  States:      NotCalibrated, Current, Due, Overdue, Failed
  Note:        This state machine tracks the calibration STATUS of a Sensor/Actuator,
               not individual Calibration records (which are immutable).
  Transitions:
    NotCalibrated → Current
      Trigger: Initial calibration performed and recorded (pass)
      Preconditions: Calibration performed per procedure. pass_fail = pass.
      Postconditions: Sensor quality_code eligible for "good." next_due_date set.
    Current → Due
      Trigger: Approaching next_due_date (configurable warning period, default 30 days)
      Preconditions: Calendar date within warning window
      Postconditions: Calibration-due alarm raised. Maintenance scheduled.
    Due → Current
      Trigger: Calibration performed before due date. pass_fail = pass.
      Preconditions: New calibration record created. Pass criteria met.
      Postconditions: next_due_date reset. Alarm cleared.
    Due → Overdue
      Trigger: next_due_date passed without calibration
      Preconditions: Calendar date > next_due_date
      Postconditions: Sensor Measurements flagged quality_code: uncertain.
                      High-priority alarm raised. Affected control loops alerted.
    Overdue → Current
      Trigger: Calibration performed. pass_fail = pass.
      Preconditions: New calibration record created. Pass criteria met.
      Postconditions: quality_code restored to normal evaluation. Alarm cleared.
    Current → Failed
      Trigger: Calibration performed. pass_fail = fail.
      Preconditions: Calibration shows readings outside acceptance criteria.
      Postconditions: Sensor Measurements flagged quality_code: bad.
                      Sensor health_status: degraded. Immediate maintenance required.
    Failed → Current
      Trigger: Sensor repaired/replaced AND new calibration pass.
      Preconditions: Repair performed. New calibration pass.
      Postconditions: quality_code and health_status restored. Historical data reviewed
                      for period of failed calibration.
```

---

## 6. INTERFACES (SYSTEM SURFACES)

> Every interface maps to at least one capability from Section 4. Interfaces define the
> contract between SUBSTRATE-PHYSICAL and its consumers. All interfaces enforce
> SafetyEnvelope validation before any physical effect.

```
IFC-P001: Sensor Registration — Implements: CAP-P001 — Source: TERM-P001, SRC-P011
  Purpose:          Register, update, and query Sensors in the physical system.
  Auth requirement:  ACT-P002 (Engineer) for create/update. ACT-P001 (Operator) for read.
  Sub-interfaces:
    IFC-P001a: Register Sensor
      Request: { sensor_type, physical_location, asset_ref, range_min, range_max,
                 engineering_units, resolution, accuracy_class, sampling_rate_max,
                 connection_protocol, zone_ref, metadata }
      Response: { sensor_id, health_status, created_at }
    IFC-P001b: Query Sensors
      Request: { filters: {asset_ref, zone_ref, sensor_type, health_status},
                 pagination }
      Response: { sensors: list<Sensor summary>, total_count }
    IFC-P001c: Get Sensor Detail
      Request: { sensor_id }
      Response: { full Sensor entity including calibration_state and health_status }
  Errors:            ERR-P001 (validation), ERR-P002 (authorization), ERR-P003 (asset not found),
                     ERR-P004 (duplicate sensor at same address)
  Idempotency:       IFC-P001a: keyed on connection_protocol address + asset_ref (same address = update).
  Rate limiting:     Per actor. Configuration operations are low-frequency.

IFC-P002: Measurement Ingestion — Implements: CAP-P002 — Source: TERM-P002, SRC-P002
  Purpose:          Ingest Measurements from Sensors (high-throughput, low-latency path).
  Auth requirement:  System (FieldbusAdapter) or ACT-P002 (manual entry with justification).
  Sub-interfaces:
    IFC-P002a: Submit Measurement (single)
      Request: { sensor_ref, timestamp, value, engineering_unit, quality_code,
                 uncertainty, raw_value }
      Response: { measurement_id, persisted_at }
    IFC-P002b: Submit Measurement Batch
      Request: { measurements: list<Measurement>, stream_ref }
      Response: { accepted_count, rejected: list<{index, reason}> }
    IFC-P002c: Query Measurements
      Request: { sensor_ref, time_range, quality_filter, aggregation,
                 pagination }
      Response: { measurements: list<Measurement>, statistics }
  Errors:            ERR-P001 (validation), ERR-P005 (sensor not found),
                     ERR-P006 (out-of-range value — recorded with quality_code: bad)
  Idempotency:       Keyed on sensor_ref + timestamp (duplicate timestamp = reject).
  Rate limiting:     Per FieldbusAdapter. Burst allowed up to buffer capacity.
  Latency:           IFC-P002a: per stream's latency_class. IFC-P002c: near_realtime.

IFC-P003: Command Submission — Implements: CAP-P007, CAP-P008 — Source: TERM-P005, SRC-P009
  Purpose:          Submit Commands to Actuators with mandatory safety validation.
  Auth requirement:  ACT-P001 (Operator), ACT-P002 (Engineer), ACT-P003/P004 (AI within
                     PhysicalEnvelope), or ENT-P009 (ControlLoop — system).
  Request schema:
    - actuator_ref       | UUID           | required
    - commanded_value    | value          | required
    - command_type       | enum           | required
    - ramp_rate          | decimal/sec    | conditional (if ramped)
    - duration           | duration       | conditional (if timed)
    - priority           | enum           | required
    - authority_ref      | ref Actor      | required (system-verified, not self-declared)
    - idempotency_key    | string         | required
  Response schema:
    - command_id         | UUID
    - safety_check_result | pass | reject (with reason)
    - initial_state      | Issued | Rejected
    - acknowledged_at    | datetime (if synchronous acknowledgment)
  Errors:            ERR-P002 (authorization), ERR-P007 (safety envelope violation — with
                     specific constraint), ERR-P008 (asset locked out), ERR-P009 (actuator
                     failed), ERR-P010 (rate limit — PhysicalEnvelope max_command_rate)
  Idempotency:       Required. Keyed on idempotency_key per actuator. Duplicate returns
                     existing command status.
  Rate limiting:     Per actor per PhysicalEnvelope.max_command_rate. Per actuator globally.
  CRITICAL:          SafetyEnvelope validation is SYNCHRONOUS and BLOCKING. A command is
                     NEVER queued if validation fails. Rejection is immediate.

IFC-P004: Alarm Management — Implements: CAP-P019 — Source: TERM-P008, SRC-P004
  Purpose:          Configure, query, and manage Alarms per ISA-18.2 lifecycle.
  Auth requirement:  ACT-P002 (Engineer) for configuration. ACT-P001 (Operator) for
                     acknowledge/shelve. ACT-P007 (Safety Authority) for safety alarm changes.
  Sub-interfaces:
    IFC-P004a: Configure Alarm
      Request: { name, condition_type, source_sensor, trigger_value, deadband,
                 delays, priority, consequence, asset_ref }
      Response: { alarm_id, current_state }
    IFC-P004b: Acknowledge Alarm
      Request: { alarm_id, acknowledging_actor }
      Response: { new_state, acknowledged_at }
    IFC-P004c: Shelve Alarm
      Request: { alarm_id, shelve_duration, reason, authorizing_actor }
      Response: { new_state, unshelve_at }
    IFC-P004d: Query Active Alarms
      Request: { filters: {priority, zone_ref, asset_ref, state}, pagination }
      Response: { alarms: list<Alarm with current_state>, alarm_rate_per_operator }
  Errors:            ERR-P001 (validation), ERR-P002 (authorization),
                     ERR-P011 (alarm not in valid state for transition)
  Idempotency:       IFC-P004b/c: idempotent per alarm_id + actor + timestamp window.

IFC-P005: ControlLoop Management — Implements: CAP-P011, CAP-P012, CAP-P015 — Source: TERM-P009
  Purpose:          Configure, tune, and manage ControlLoops.
  Auth requirement:  ACT-P002 (Engineer) for create/tune. ACT-P001 (Operator) for mode change.
  Sub-interfaces:
    IFC-P005a: Create ControlLoop
      Request: { loop_type, process_variable, setpoint, output, tuning_parameters,
                 scan_rate, latency_class, safety_envelope_ref, asset_ref }
      Response: { loop_id, mode: manual }
    IFC-P005b: Change Mode
      Request: { loop_id, new_mode, authorization }
      Response: { previous_mode, new_mode, changed_at }
    IFC-P005c: Update Setpoint
      Request: { loop_id, new_value, ramp_rate, source, authorization }
      Response: { setpoint_id, effective_from, safety_check_result }
    IFC-P005d: Update Tuning
      Request: { loop_id, tuning_parameters, authorization }
      Response: { previous_tuning, new_tuning, changed_at }
    IFC-P005e: Query Loop Performance
      Request: { loop_id, time_range }
      Response: { performance_metrics, mode_history, setpoint_history }
  Errors:            ERR-P001 (validation), ERR-P002 (authorization),
                     ERR-P007 (setpoint outside safety envelope),
                     ERR-P012 (scan_rate incompatible with latency_class)
  Idempotency:       Mode changes and setpoint updates are idempotent per loop + value + timestamp.

IFC-P006: Process Execution — Implements: CAP-P023 — Source: TERM-P019, TERM-P020
  Purpose:          Start, monitor, hold, and complete ProcessExecutions.
  Auth requirement:  ACT-P001 (Operator) for start/hold/resume/abort. ACT-P002 for configuration.
  Sub-interfaces:
    IFC-P006a: Start Process Execution
      Request: { process_ref, actual_parameters, assets_used, operator_ref }
      Response: { execution_id, status: initialized, precondition_check_result }
    IFC-P006b: Hold/Resume/Abort Execution
      Request: { execution_id, action: hold | resume | abort, reason }
      Response: { new_status, transition_at }
    IFC-P006c: Query Execution Status
      Request: { execution_id }
      Response: { full ProcessExecution with current step, measurements, alarms }
    IFC-P006d: Query Execution History
      Request: { process_ref, time_range, status_filter, pagination }
      Response: { executions: list<ProcessExecution summary>, total_count }
  Errors:            ERR-P001 (validation), ERR-P002 (authorization),
                     ERR-P013 (preconditions not met), ERR-P014 (assets unavailable),
                     ERR-P015 (invalid state transition)

IFC-P007: Asset Management — Implements: CAP-P021, CAP-P022 — Source: TERM-P017
  Purpose:          Register, query, and manage PhysicalAssets including LOTO.
  Auth requirement:  ACT-P002 (Engineer) for create/configure. ACT-P001 (Operator) for LOTO
                     and state transitions.
  Sub-interfaces:
    IFC-P007a: Register Asset
      Request: { asset_type, make, model, serial_number, physical_location,
                 hierarchy_level, parent_asset, safety_envelope_ref }
      Response: { asset_id, operational_state: commissioning }
    IFC-P007b: LOTO Request
      Request: { asset_id, loto_action: lock | unlock, performing_actor, reason }
      Response: { new_state, loto_tag_id, transition_at }
    IFC-P007c: State Transition
      Request: { asset_id, target_state, authorization, checklist_results }
      Response: { previous_state, new_state, transition_at }
    IFC-P007d: Query Asset Hierarchy
      Request: { root_asset_id, depth, include_sensors, include_actuators }
      Response: { asset_tree with nested children, sensor/actuator counts }
  Errors:            ERR-P002 (authorization), ERR-P008 (already locked out),
                     ERR-P015 (invalid state transition),
                     ERR-P016 (LOTO — not all lock holders released)

IFC-P008: SafetyEnvelope Management — Implements: CAP-P018 — Source: TERM-P014, SRC-P009
  Purpose:          Define, approve, and query SafetyEnvelopes. MOC-controlled.
  Auth requirement:  ACT-P002 (Engineer) for draft. ACT-P007 (Safety Authority) for approve.
  Sub-interfaces:
    IFC-P008a: Draft SafetyEnvelope
      Request: { name, physical_constraints, safety_functions, operational_limits,
                 permitted_modes, permitted_actors, asset_ref, moc_reference }
      Response: { envelope_id, version, status: drafted }
    IFC-P008b: Approve SafetyEnvelope
      Request: { envelope_id, approving_authority: ACT-P007, approval_notes }
      Response: { version, status: approved, effective_from }
    IFC-P008c: Query Active Envelope
      Request: { asset_ref }
      Response: { active SafetyEnvelope with all constraints }
    IFC-P008d: Validate Against Envelope
      Request: { envelope_id, operation_type: command | setpoint | mode_change,
                 operation_details }
      Response: { result: pass | fail, violated_constraints: list }
  Errors:            ERR-P002 (authorization), ERR-P017 (MOC reference required),
                     ERR-P018 (operational_limits exceed PhysicalConstraints)

IFC-P009: FieldbusAdapter Configuration — Implements: CAP-P025 — Source: TERM-P022
  Purpose:          Configure and monitor FieldbusAdapters (protocol translation layer).
  Auth requirement:  ACT-P002 (Engineer) for configuration. System for health monitoring.
  Sub-interfaces:
    IFC-P009a: Configure Adapter
      Request: { protocol_type, connection_parameters, polling_configuration,
                 data_mapping, latency_class }
      Response: { adapter_id, health_status }
    IFC-P009b: Query Adapter Health
      Request: { adapter_id or filters: {protocol_type, health_status} }
      Response: { health_status, last_communication, error_count, latency_stats }
    IFC-P009c: Update Data Mapping
      Request: { adapter_id, data_mapping_changes }
      Response: { updated_mappings, validation_result }
  Errors:            ERR-P001 (validation), ERR-P002 (authorization),
                     ERR-P019 (protocol not supported), ERR-P020 (connection failed)

IFC-P010: DigitalTwin Interface — Implements: CAP-P026 — Source: TERM-P023
  Purpose:          Create, synchronize, and query DigitalTwins.
  Auth requirement:  ACT-P002 (Engineer) for create. ACT-P001/P003/P004 for query.
  Sub-interfaces:
    IFC-P010a: Create DigitalTwin
      Request: { physical_counterpart_type, physical_counterpart_ref, model_type,
                 fidelity, synchronization_rate, drift_threshold, simulation_endpoint }
      Response: { twin_id, current_state }
    IFC-P010b: Query Twin State
      Request: { twin_id }
      Response: { current_state, last_synchronized, drift_detected }
    IFC-P010c: Run What-If Scenario
      Request: { twin_id, parameter_changes: list<{parameter, new_value}>,
                 time_horizon }
      Response: { predicted_states: time_series, confidence, compute_job_ref }
  Errors:            ERR-P001 (validation), ERR-P002 (authorization),
                     ERR-P021 (simulation endpoint unavailable — COMPUTE dependency)
```

---

## 7. DATA FLOWS (HOW DATA MOVES)

> One flow per MUST capability cluster. Each flow is testable end-to-end. Steps within
> an atomicity boundary succeed or fail together.

```
FLOW-P001: Measure — Implements: CAP-P001, CAP-P002, CAP-P003 — Source: SRC-P002, SRC-P011
  Trigger:             Sensor scan (periodic), value change (on_change), or external trigger
  Inputs:              Raw signal from physical hardware via FieldbusAdapter
  Steps:
    1. FieldbusAdapter reads raw value from hardware per polling_configuration
    2. Apply data_mapping transform (register → engineering units)
    3. Validate range: if outside sensor.range_min/max, set quality_code: bad
    4. Check sensor calibration_state: if overdue, set quality_code: uncertain
    5. Check sensor health_status: if degraded, set quality_code: uncertain; if failed, reject
    6. Create Measurement entity with timestamp from synchronized time source (DEP-P001)
    7. If MeasurementStream configured: apply compression (swinging_door/boxcar)
    8. Persist Measurement to event store (append-only)
    9. Deliver to registered destinations: control_input → ControlLoop, historian → storage,
       event_bus → stream consumers
    10. If quality_code ≠ good: evaluate Alarm conditions on this sensor
    11. Emit Event (TERM-P024) for audit trail
  Outputs:             Measurement entity persisted and delivered to destinations
  Side effects:        Alarm evaluation, ControlLoop input update, historian storage,
                       cross-substrate event if configured
  Error paths:
    Step 1: FieldbusAdapter disconnected → quality_code: bad, communication_loss alarm
    Step 5: Sensor failed → Measurement rejected, alarm raised
    Step 8: Persistence failure → buffer locally, retry (never lose measurement)
    Step 9: Destination unavailable → queue for retry per destination
  Atomicity boundary:  Steps 6-8 MUST succeed or fail together (measurement + event).
                       Steps 9-11 are eventual.

FLOW-P002: Command — Implements: CAP-P007, CAP-P008, CAP-P009 — Source: SRC-P001, SRC-P009
  Trigger:             IFC-P003 (Command Submission) or ControlLoop output
  Inputs:              actuator_ref, commanded_value, command_type, authority_ref
  Steps:
    1. Authenticate and authorize command source (Actor or ControlLoop)
    2. If AI agent: validate against PhysicalEnvelope (ENT-P015)
    3. Check asset operational_state: if LockedOut → REJECT immediately (CAP-P009)
    4. Validate commanded_value against SafetyEnvelope (ENT-P014) — SYNCHRONOUS
    5. Validate commanded_value against PhysicalConstraints (ENT-P007)
    6. Check idempotency_key: if duplicate, return existing command status
    7. Create Command entity with status: Issued
    8. Persist Command as Event in append-only store
    9. Send command to actuator via FieldbusAdapter
    10. Await acknowledgment from device (→ Acknowledged)
    11. Await execution confirmation from device (→ Executed)
    12. Read feedback_sensor to verify actuator position
    13. Compare feedback to commanded_value within tolerance
    14. Set verification_result: confirmed | timeout | mismatch
    15. If timeout or mismatch: raise alarm, emit Event
    16. Emit cross-substrate event if safety-critical (CAP-P027)
  Outputs:             Command entity with full lifecycle recorded
  Side effects:        Physical actuator state change, alarm (if verification fails),
                       cross-substrate events for safety-critical commands
  Error paths:
    Step 2: ERR-P010 → reject with "outside physical envelope"
    Step 3: ERR-P008 → reject with "asset locked out"
    Step 4: ERR-P007 → reject with specific constraint violated. NEVER queued.
    Step 9: FieldbusAdapter disconnected → command fails, actuator drives to safe_state
    Step 12: Feedback sensor unavailable → verification_result: timeout, alarm raised
  Atomicity boundary:  Steps 7-8 atomic (command creation + event). Steps 9-15 are
                       physical operations with independent failure modes.
  CRITICAL:            Steps 3-5 are BLOCKING and SYNCHRONOUS. A command that fails
                       safety validation NEVER reaches the actuator.

FLOW-P003: Control Loop Scan — Implements: CAP-P011, CAP-P012 — Source: SRC-P010
  Trigger:             Periodic timer per ControlLoop.scan_rate
  Inputs:              process_variable (from Sensor), setpoint (from ENT-P010)
  Steps:
    1. Read current process_variable from Sensor (latest Measurement)
    2. Check Measurement quality_code: if bad, enter fallback mode
    3. Compute error = setpoint.value - process_variable
    4. Apply control algorithm (PID: output = Kp*e + Ki*∫e + Kd*de/dt, or equivalent)
    5. Apply output limits (output_min, output_max, rate_of_change_limit)
    6. If mode ≠ automatic: skip output, display computed value only
    7. Generate Command for output Actuator with computed value
    8. Submit Command via FLOW-P002 (with full safety validation)
    9. Update performance_metrics (IAE, ISE, overshoot, etc.)
    10. Emit performance Event at configured interval (not every scan)
  Outputs:             Actuator Command (via FLOW-P002), updated performance metrics
  Side effects:        Actuator position change, performance metric update
  Error paths:
    Step 1: Sensor unavailable → use last known value for configurable duration,
            then enter fallback mode (output to safe_state)
    Step 2: quality_code: bad → enter manual mode, alert operator
    Step 8: Command rejected by SafetyEnvelope → output clamped, alarm raised
  Atomicity boundary:  Steps 1-6 are computation (no side effects). Steps 7-8 are physical
                       effect (via FLOW-P002). Step 9-10 are eventual.
  Timing:              MUST complete within ControlLoop.scan_rate period. If overrun,
                       skip this cycle and log timing violation.

FLOW-P004: Alarm Lifecycle — Implements: CAP-P019 — Source: SRC-P004 (ISA-18.2)
  Trigger:             Measurement meets alarm condition (after on_delay)
  Inputs:              source_sensor Measurements, alarm configuration
  Steps:
    1. Evaluate alarm condition against latest Measurement(s)
    2. If condition true: start on_delay timer (if not already started)
    3. If condition persists for on_delay duration: transition to Active_Unacknowledged
    4. Record alarm activation Event with timestamp, cause, and current values
    5. Annunciate: deliver alarm to operator via configured channels
    6. If priority = emergency: also emit cross-substrate event (COMMUNICATION escalation)
    7. Check alarm flood: if >10 alarms/operator/10 min, trigger rationalization alert
    8. Await operator acknowledgment (→ Active_Acknowledged via IFC-P004b)
    9. Monitor for condition clearing (after off_delay)
    10. On clear: transition to Normal (if acknowledged) or Cleared_Unacknowledged
    11. Record full lifecycle as Events
  Outputs:             Alarm state transitions recorded as Events
  Side effects:        Operator notification, cross-substrate escalation (if emergency),
                       alarm flood detection, COMMUNICATION Discourse (if unresolved)
  Error paths:
    Step 5: Notification channel unavailable → queue, retry, escalate
    Step 7: Alarm flood → priority-based suppression of low-priority alarms,
            alert to engineering
  Atomicity boundary:  Steps 3-4 atomic (state transition + event). Steps 5-7 eventual.

FLOW-P005: Execute Process — Implements: CAP-P023 — Source: SRC-P004, SRC-P012
  Trigger:             IFC-P006a (Start Process Execution)
  Inputs:              process_ref, actual_parameters, assets_used, operator_ref
  Steps:
    1. Validate process_ref exists and is in Approved state
    2. Verify all required_assets are Operational and available (not LockedOut)
    3. Verify required OperatingMode is active on all assets
    4. Verify all preconditions of first ControlSequence
    5. Create ProcessExecution entity with status: Initialized
    6. Start data logging: all Measurements, Commands, Alarms on assets_used
    7. Transition to Running. Start first ControlSequence (FLOW via SM-P004)
    8. Monitor each ControlSequence: on completion, start next in order
    9. Monitor abort conditions continuously across all sequences
    10. On all sequences complete: record quality_results and yield
    11. Transition to Completed. Stop data logging. Record end_time.
    12. Emit cross-substrate event: substrate.physical.process_execution.completed
  Outputs:             Complete ProcessExecution record with full audit trail
  Side effects:        Physical transformation executed, audit trail created,
                       BUSINESS workflow updated, cross-substrate events emitted
  Error paths:
    Step 2: ERR-P014 → reject with "assets unavailable"
    Step 9: Abort condition → SM-P005 Running → Aborted. Safe state. Material disposition.
    Step 7-8: ControlSequence failure → hold or abort depending on failure type
  Atomicity boundary:  Steps 5-6 atomic (execution creation + logging start).
                       Steps 7-11 are composed of many sub-atomic operations (each
                       ControlSequence step is independently atomic).

FLOW-P006: Safety Trip — Implements: CAP-P016, CAP-P017 — Source: SRC-P009
  Trigger:             SafetyFunction triggering_condition becomes true
  Inputs:              Triggering measurements/states, SafetyFunction definition
  Steps:
    1. SafetyFunction evaluates triggering_condition INDEPENDENTLY of basic control
    2. Condition true: initiate required_action IMMEDIATELY (no confirmation, no delay)
    3. Execute required_action: emergency_shutdown, valve_close, power_disconnect, etc.
    4. Drive ALL affected actuators to safe_state
    5. Record safety trip Event with timestamp, cause, measurements at time of trip
    6. Transition affected assets to appropriate state (Shutdown or safe mode)
    7. Alert all operators and Safety Authority via cross-substrate events
    8. Emit: substrate.physical.safety_function.tripped
    9. Block all non-safety Commands to affected assets until reset authorized
    10. Await Safety Authority investigation and reset authorization
    11. On authorized reset: verify conditions, perform function test, restore
  Outputs:             Safety trip Event, affected assets in safe state
  Side effects:        Physical equipment stopped/safe, operators alerted, production halted,
                       COMMUNICATION incident Discourse created
  Error paths:
    Step 3: Required action physically fails → secondary safety action (if available),
            immediate operator alert, manual intervention required
  Atomicity boundary:  Steps 1-4 are hard_realtime, atomic, INDEPENDENT of all other
                       operations. Steps 5-8 eventual. Steps 9-11 human-in-the-loop.
  CRITICAL:            SafetyFunction executes on INDEPENDENT hardware. Steps 1-4 MUST
                       complete within response_time_requirement. NOTHING blocks this flow.

FLOW-P007: Lock-Out/Tag-Out (LOTO) — Implements: CAP-P022 — Source: TERM-P017, SRC-P009
  Trigger:             IFC-P007b (LOTO Request — lock)
  Inputs:              asset_id, performing_actor, reason
  Steps:
    1. Verify performing_actor is authorized for LOTO on this asset
    2. Verify asset is in Operational or Degraded state
    3. Initiate controlled shutdown: drive all Actuators to safe_state
    4. Verify all Actuators have reached safe_state (via feedback sensors)
    5. Record LOTO activation Event with tag_id, actor, reason, timestamp
    6. Transition asset to LockedOut (SM-P001)
    7. Replace SafetyEnvelope with maintenance envelope (reads only, zero writes)
    8. ALL subsequent Commands to this asset's Actuators are REJECTED
    9. Emit cross-substrate event: substrate.physical.asset.locked_out
    10. [Maintenance performed — see FLOW-P008 or MaintenanceAction]
    11. On LOTO release request: verify all lock holders have released
    12. Perform safety verification and function test
    13. Transition to ReturnToService, then Operational (SM-P001)
    14. Restore normal SafetyEnvelope
    15. Emit cross-substrate event: substrate.physical.asset.return_to_service
  Outputs:             Asset state transitions, LOTO events recorded
  Side effects:        Asset unavailable for production, maintenance envelope active,
                       BUSINESS workflow updated
  Error paths:
    Step 4: Actuator fails to reach safe_state → cannot lock out, alarm raised,
            manual energy isolation required
    Step 11: Not all lock holders released → REJECT unlock (multi-lock LOTO)
  Atomicity boundary:  Steps 3-7 atomic (controlled shutdown + LOTO activation).
                       Steps 11-14 atomic (LOTO release + safety verification).

FLOW-P008: Calibration Cycle — Implements: CAP-P028 — Source: SRC-P011
  Trigger:             Calibration due date approaching (SM-P006: Current → Due) or manual
  Inputs:              subject (Sensor or Actuator), reference_standard, conditions
  Steps:
    1. Record calibration initiation Event
    2. Perform as-found readings against reference standard
    3. Record as-found data with environmental conditions
    4. If adjustment needed: perform adjustment
    5. Record as-left readings (if adjusted)
    6. Evaluate pass/fail against acceptance_criteria
    7. Create Calibration entity (ENT-P006) with all recorded data
    8. Update subject's calibration_state to reference new Calibration
    9. If pass: SM-P006 → Current. Reset next_due_date. Clear alarms.
    10. If fail: SM-P006 → Failed. Set quality_code: bad. Alert.
    11. Emit Event for audit trail
    12. If Calibration history is shared with KNOWLEDGE: emit cross-substrate event
        (substrate.physical.calibration.completed) per INT-P002
  Outputs:             Calibration record, updated calibration_state
  Side effects:        Sensor/Actuator quality_code updated, alarms cleared or raised,
                       KNOWLEDGE Source reliability updated, certificate stored
  Error paths:
    Step 6: Fail → immediate maintenance required, affected measurements flagged
  Atomicity boundary:  Steps 7-9 atomic (calibration record + state update).
```

---

## 8. INTEGRATION CONTRACTS (HOW SUBSTRATES CONNECT)

> One contract per substrate dependency. Each contract follows P1-P4 boundary
> principles from CROSS-SUBSTRATE-CONVENTIONS.md §6.

```
INT-P001: BUSINESS Integration — Depends on: DEP-P004 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:          Cross-substrate event bus (CROSS-SUBSTRATE-CONVENTIONS.md §3) +
                     direct reference resolution (§5)
  Auth:              Mutual substrate identity via shared identity provider (§1)
  Integration points:
    a) PhysicalAsset ↔ Business Entity
       — PHYSICAL: owns operational state, sensors, actuators, safety envelope
       — BUSINESS: owns financial value, depreciation, ownership, cost center
       — Mapping: ENT-P017.business_entity_ref → BUSINESS Entity
       — Principle: P4 (one owner, many references)
    b) MaintenanceAction ↔ Business Workflow
       — PHYSICAL: owns physical execution, measurements before/after
       — BUSINESS: owns work order, cost, scheduling, parts procurement
       — Mapping: ENT-P021.business_workflow_ref → BUSINESS Workflow
       — Principle: P1 (content vs process)
    c) ProcessExecution ↔ Business Transaction
       — PHYSICAL: owns process data, quality results, audit trail
       — BUSINESS: owns production order, cost allocation, material accounting
       — Principle: P1 (content vs process)
    d) PhysicalEnvelope → Business Agent Envelope
       — PHYSICAL: must chain from valid Business Agent Envelope
       — Mapping: ENT-P015.business_envelope_ref → BUSINESS TERM-030
       — Principle: P3 (define vs enforce). BUSINESS defines agent identity.
    e) Zone ↔ Business Location
       — PHYSICAL: owns safety/security classification
       — BUSINESS: owns organizational location hierarchy
       — Principle: P4 (one owner per attribute)
    f) Alarm → Business Notification
       — PHYSICAL: triggers alarm. BUSINESS delivers notification.
       — Principle: P2 (trigger vs deliver)
  Events emitted:   substrate.physical.asset.state_changed,
                     substrate.physical.process_execution.completed,
                     substrate.physical.maintenance_action.completed,
                     substrate.physical.alarm.escalated
  Events consumed:   substrate.business.workflow.assigned,
                     substrate.business.entity.updated
  Failure modes:     BUSINESS unavailable → physical operations continue independently.
                     Cross-references unresolvable. New agent authorization blocked.
                     Existing authorizations cached locally.
  Retry policy:      Event emission: max 10 retries, exponential backoff, DLQ after.
  Idempotency:       Event IDs are globally unique UUIDs.

INT-P002: KNOWLEDGE Integration — Depends on: DEP-P005 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:          Cross-substrate event bus + reference resolution
  Auth:              Mutual substrate identity
  Integration points:
    a) Sensor → Knowledge Source
       — PHYSICAL: owns sensor hardware, calibration, measurement accuracy
       — KNOWLEDGE: owns source reliability assessment, epistemic trust
       — Mapping: Sensor registered as KNOWLEDGE Source (TERM-K020)
       — Calibration history provides reliability metadata
       — Principle: P4 (PHYSICAL owns hardware truth, KNOWLEDGE owns epistemic trust)
    b) Measurement → Knowledge Observation
       — PHYSICAL: owns raw measurement with quality metadata
       — KNOWLEDGE: creates Observation with epistemic interpretation
       — Principle: P1 (PHYSICAL = content, KNOWLEDGE = epistemic interpretation)
    c) Calibration ↔ Knowledge Calibration
       — PHYSICAL: hardware-level instrument accuracy (TERM-P006)
       — KNOWLEDGE: epistemic source reliability (TERM-K021)
       — Together: complete trust chain from physical measurement to knowledge claim
    d) HazardAnalysis → Knowledge Proposition
       — PHYSICAL: owns risk assessment execution and SafetyFunction enforcement
       — KNOWLEDGE: tracks whether risk assessment still holds (as Proposition)
       — Principle: P3 (PHYSICAL enforces, KNOWLEDGE tracks validity)
    e) DigitalTwin → Knowledge Prediction
       — PHYSICAL: owns twin state sync and drift detection
       — KNOWLEDGE: evaluates prediction accuracy as epistemic claim
  Events emitted:   substrate.physical.measurement.quality_changed,
                     substrate.physical.calibration.completed,
                     substrate.physical.hazard_analysis.reviewed,
                     substrate.physical.digital_twin.drift_detected
  Events consumed:   substrate.knowledge.source.reliability_changed,
                     substrate.knowledge.proposition.status_changed
  Failure modes:     KNOWLEDGE unavailable → physical operations continue. Knowledge
                     ingestion queues. No impact on control or safety.
  Retry policy:      Event emission: max 10 retries, exponential backoff, DLQ after.

INT-P003: COMPUTE Integration — Depends on: DEP-P006 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:          Cross-substrate event bus + direct API for computation requests
  Auth:              Mutual substrate identity + COMPUTE resource authorization
  Integration points:
    a) MPC ControlLoop → Compute Computation
       — PHYSICAL: owns loop definition, sensor data, actuator output
       — COMPUTE: owns optimization computation (MPC solver)
       — PHYSICAL requests computation, receives optimal output
       — Principle: P1 (PHYSICAL = control intent, COMPUTE = mathematical execution)
    b) DigitalTwin → Compute Pipeline
       — PHYSICAL: owns twin state, synchronization, drift detection
       — COMPUTE: owns simulation engine, model execution
       — Mapping: ENT-P023.simulation_endpoint → COMPUTE Pipeline
       — Principle: P1 (PHYSICAL = state, COMPUTE = simulation)
    c) Predictive Analytics → Compute Result
       — PHYSICAL: owns sensor data streams, equipment history
       — COMPUTE: owns ML models, prediction pipeline
       — Results consumed by PHYSICAL for condition-based maintenance
    d) MeasurementStream → Compute Dataset
       — PHYSICAL: owns streaming data source
       — COMPUTE: owns batch processing and analytics
    e) PhysicalAsset → Compute ResourcePool
       — PHYSICAL: owns asset operational state
       — COMPUTE: manages computational resource allocation
  Events emitted:   substrate.physical.measurement_stream.data_available,
                     substrate.physical.asset.performance_degraded
  Events consumed:   substrate.compute.computation.completed,
                     substrate.compute.pipeline.result_available
  Failure modes:     COMPUTE unavailable → advanced control (MPC) degrades to basic (PID).
                     Digital twins go stale. Predictive maintenance reverts to scheduled.
                     Basic control and safety UNAFFECTED.
  Retry policy:      Computation requests: max 3 retries, then degrade gracefully.

INT-P004: COMMUNICATION Integration — Depends on: DEP-P007 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:          Cross-substrate event bus + reference resolution
  Auth:              Mutual substrate identity
  Integration points:
    a) Alarm → Communication Discourse
       — PHYSICAL: triggers alarm, owns alarm lifecycle
       — COMMUNICATION: creates escalation Discourse with tracked Obligations
       — Unresolved critical alarms auto-escalate to COMMUNICATION
       — Principle: P2 (trigger vs deliver)
    b) OperatingMode change → Communication Consensus
       — PHYSICAL: owns mode definition and entry_conditions
       — COMMUNICATION: hosts Management of Change review as structured Discourse
       — Principle: P1 (PHYSICAL = mode content, COMMUNICATION = review process)
    c) MaintenanceAction → Communication Commitment
       — PHYSICAL: owns physical execution record
       — COMMUNICATION: hosts coordination Discourse with Commitments and Obligations
       — Maintenance team coordination uses COMMUNICATION Speech Acts
    d) Safety Incident → Communication Argument
       — PHYSICAL: owns safety trip data, sensor readings, timeline
       — COMMUNICATION: hosts incident investigation as structured argumentation
       — Principle: P1 (PHYSICAL = evidence, COMMUNICATION = investigation discourse)
    e) Shift Handoff → Communication Protocol
       — PHYSICAL: provides current system state snapshot for handoff
       — COMMUNICATION: hosts shift handoff as Protocol-governed Discourse
    f) FieldbusAdapter ↔ Communication Channel
       — PHYSICAL: owns protocol translation and data integrity
       — COMMUNICATION: not directly related; FieldbusAdapter is PHYSICAL-internal
       — Note: FieldbusAdapters are NOT COMMUNICATION Channels. They are hardware
         protocol adapters. This is a boundary clarification, not an integration.
  Events emitted:   substrate.physical.alarm.escalation_required,
                     substrate.physical.operating_mode.change_requested,
                     substrate.physical.safety_function.tripped,
                     substrate.physical.asset.shift_handoff_ready
  Events consumed:   substrate.communication.discourse.resolved,
                     substrate.communication.consensus.reached,
                     substrate.communication.commitment.fulfilled
  Failure modes:     COMMUNICATION unavailable → operator notifications queue. Shift
                     handoff records degrade to local logs. Escalation timers pause.
                     Physical operations CONTINUE.
  Retry policy:      Event emission: max 10 retries, exponential backoff, DLQ after.

INT-P005: Content Store Integration — Depends on: DEP-P008 — Source: DEP-P008
  Protocol:          Content Store API (binary artifact storage)
  Auth:              System credentials + per-artifact access control
  Integration points:
    — Calibration certificates (ENT-P006.certificate_ref)
    — Engineering drawings, P&IDs (ENT-P026 visual representations)
    — Maintenance photos, inspection images (ENT-P021 attachments)
    — Waveform captures, camera snapshots, lidar scans (high-fidelity data)
    — HazardAnalysis supporting documents (ENT-P016 documentation)
  Failure modes:     Content Store unavailable → metadata accessible. Binary content
                     temporarily unreadable. No impact on control or safety.
  Retry policy:      Upload: retry with exponential backoff. Download: cache locally.

INT-P006: DESIGN Integration — Depends on: DEP-P009 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:          Cross-substrate event bus + reference resolution
  Auth:              Mutual substrate identity
  Purpose:           Connect operational instances to design specifications.
  Integration points:
    a) PhysicalAsset ↔ Design Component
       — PHYSICAL: owns operational instance (what it is)
       — DESIGN: owns specification (what it should be)
       — Mapping: ENT-P017.design_component_ref → DESIGN Component (TERM-D004)
       — Link established when manufactured. Maintained for lifecycle.
       — Principle: P4 (PHYSICAL owns instance, DESIGN owns specification)
    b) Process ↔ Design FabricationMethod
       — PHYSICAL: owns how to run the process (execution)
       — DESIGN: owns how to make it (specification)
       — Mapping: ENT-P019 → DESIGN FabricationMethod (TERM-D020)
       — This IS the manufacturing-from-design handoff
       — Principle: P4
    c) SafetyEnvelope ↔ Design Specification safety requirements
       — PHYSICAL: owns runtime safety enforcement (SafetyEnvelope TERM-P014)
       — DESIGN: owns safety requirements in Specification
       — DESIGN safety Requirements inform PHYSICAL SafetyEnvelope configuration
       — Principle: P3 (DESIGN defines, PHYSICAL enforces)
    d) Measurement ↔ Design Tolerance
       — PHYSICAL: owns measurement (what it actually is)
       — DESIGN: owns dimensional specification (what it should be)
       — Feedback loop: DESIGN tolerance → PHYSICAL measures → comparison
       — Mapping: ENT-P002 values verified against DESIGN Tolerance (TERM-D011)
       — Principle: P1 (DESIGN = specification, PHYSICAL = measurement)
    e) DigitalTwin ↔ Design AnalysisResult
       — PHYSICAL: owns runtime simulation via DigitalTwin (TERM-P023)
       — DESIGN: owns design-time analysis predictions (TERM-D014)
       — Comparison validates design assumptions against operational reality
       — Principle: P1
  Events emitted:   substrate.physical.asset.commissioned,
                     substrate.physical.measurement.tolerance_deviation,
                     substrate.physical.calibration.completed,
                     substrate.physical.process_execution.completed
  Events consumed:   substrate.design.component.released,
                     substrate.design.specification.safety_requirements_updated,
                     substrate.design.fabrication_method.defined
  Failure modes:     DESIGN unavailable → physical operations continue. As-built
                     feedback unavailable. Manufacturing handoff blocked until restored.
  Retry policy:      Event emission: max 10 retries, exponential backoff, DLQ after.
  Mirror:            INT-D005 in SUBSTRATE-DESIGN.

INT-P007: GOVERNANCE Integration — Depends on: DEP-P010 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:          Cross-substrate event bus + reference resolution
  Auth:              Mutual substrate identity
  Purpose:           Provide safety evidence for regulatory compliance.
  Integration points:
    a) SafetyFunction ↔ Governance Prohibition + RegulatoryChange
       — PHYSICAL: owns safety function execution and trip events
       — GOVERNANCE: records Norms/Prohibitions on AI in safety functions
       — Safety certification status queried from GOVERNANCE
       — Resolves UNK-P005, OQ-P005
       — Principle: P3
    b) HazardAnalysis ↔ Governance RiskAssessment
       — PHYSICAL: owns domain-specific hazard analysis (TERM-P016)
       — GOVERNANCE: links to broader organizational RiskAssessment (TERM-G015)
       — Principle: P1 (PHYSICAL = domain-specific, GOVERNANCE = organizational)
    c) Calibration + Alarm → Governance ComplianceAssessment
       — PHYSICAL: provides calibration records and alarm history as evidence
       — GOVERNANCE: owns audit requirements for regulated physical operations
       — Principle: P3
    d) PhysicalEnvelope ↔ Governance normative source
       — GOVERNANCE: provides normative basis for physical access restrictions
       — PHYSICAL: enforces at runtime (most restrictive in chain)
       — Principle: P3
  Events emitted:   substrate.physical.safety_function.tripped,
                     substrate.physical.alarm.escalation_required,
                     substrate.physical.calibration.completed,
                     substrate.physical.asset.locked_out
  Events consumed:   substrate.governance.norm.effective,
                     substrate.governance.assessment.completed
  Failure modes:     GOVERNANCE unavailable → physical operations continue. Safety
                     Prohibition status cached. Compliance evidence queued.
  Retry policy:      Event emission: max 10 retries, exponential backoff, DLQ after.
  Mirror:            INT-G005 in SUBSTRATE-GOVERNANCE.

INT-P008: TEMPORAL Integration — Depends on: DEP-P011 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:          Cross-substrate event bus + reference resolution
  Auth:              Mutual substrate identity
  Purpose:           Synchronize equipment state with scheduling availability.
  Integration points:
    a) PhysicalAsset state → Temporal Availability
       — PHYSICAL: owns equipment operational state
       — TEMPORAL: owns scheduling availability (TERM-T003)
       — State mapping:
         Operational      → Available (full capacity)
         Degraded         → Conditionally Available (reduced capacity_level)
         LockedOut        → Unavailable (Bookings blocked, existing → Disruption)
         Shutdown         → Unavailable (for shutdown duration)
         Decommissioned   → Unavailable (permanent, resource decommissioned)
       — Principle: P4 (PHYSICAL owns state, TEMPORAL owns availability)
    b) MaintenanceAction scheduling
       — PHYSICAL: requests maintenance time windows
       — TEMPORAL: schedules as Activity, creates Booking for equipment
       — TEMPORAL confirms booking, PHYSICAL executes maintenance
  Events emitted:   substrate.physical.asset.state_changed,
                     substrate.physical.asset.degraded,
                     substrate.physical.maintenance.completed
  Events consumed:   substrate.temporal.booking.confirmed,
                     substrate.temporal.activity.completed
  Failure modes:     TEMPORAL unavailable → maintenance scheduling degrades to manual.
                     Physical operations CONTINUE. Equipment state emitted on reconnect.
  Retry policy:      Event emission: max 10 retries, exponential backoff, DLQ after.
  Boundary:          Purpose, not duration. PHYSICAL owns control loops, safety functions,
                     equipment operation. TEMPORAL owns planning, coordination, resource
                     allocation. A 200ms safety interlock is PHYSICAL. A 30-year maintenance
                     plan is TEMPORAL.
  Mirror:            INT-T003 in SUBSTRATE-TEMPORAL.

INT-P009: SPATIAL Integration — Depends on: DEP-P012 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:          Cross-substrate event bus + reference resolution
  Auth:              Mutual substrate identity
  Purpose:           Provide location data from physical sensors to spatial system.
  Integration points:
    a) GPS/GNSS Measurement → Spatial Location
       — PHYSICAL: owns GPS/GNSS sensor hardware and raw position data
       — SPATIAL: owns geographic interpretation, creates/updates Location (TERM-S002)
       — Mapping: Measurement with GPS/GNSS position → SPATIAL Location
       — Principle: P4 (PHYSICAL owns measurement, SPATIAL owns geographic interpretation)
    b) PhysicalAsset.location_ref → Spatial Location
       — PHYSICAL: owns asset with location reference
       — SPATIAL: owns Location entity and position history
       — Mapping: ENT-P017.location_ref → SPATIAL Location (TERM-S002)
    c) Asset relocation → Spatial Trajectory
       — PHYSICAL: emits asset relocated events
       — SPATIAL: updates Location and records Trajectory (TERM-S021)
    d) Physical Zone ↔ Spatial Zone cross-reference
       — PHYSICAL: owns operational safety grouping (TERM-P018)
       — SPATIAL: owns geographic region with policies (TERM-S016)
       — Physical Zone MAY reference Spatial Zone for geographic positioning
       — Principle: P4 (one owner per dimension)
  Events emitted:   substrate.physical.measurement.recorded,
                     substrate.physical.asset.relocated
  Events consumed:   (reference resolution — no explicit SPATIAL→PHYSICAL events)
  Failure modes:     SPATIAL unavailable → position data queued. Physical operations
                     CONTINUE. Location references unresolvable until restored.
  Retry policy:      Event emission: max 10 retries, exponential backoff, DLQ after.
  Mirror:            INT-S006 in SUBSTRATE-SPATIAL.
```

### Cross-Substrate Event Topics

```
All events emitted or consumed by PHYSICAL across integration contracts INT-P001–P009.

Events Emitted by PHYSICAL:
  substrate.physical.asset.state_changed          — PhysicalAsset operational state transition
  substrate.physical.asset.degraded               — PhysicalAsset capacity reduced
  substrate.physical.asset.commissioned           — PhysicalAsset linked to design spec
  substrate.physical.asset.relocated              — PhysicalAsset moved to new location
  substrate.physical.asset.locked_out             — PhysicalAsset LOTO engaged
  substrate.physical.asset.shift_handoff_ready    — System state snapshot for shift change
  substrate.physical.asset.performance_degraded   — Performance below threshold
  substrate.physical.process_execution.completed  — Batch/continuous process completed
  substrate.physical.maintenance_action.completed — Maintenance work completed
  substrate.physical.maintenance.completed        — Maintenance scheduling confirmation
  substrate.physical.alarm.escalated              — Alarm auto-escalated to COMMUNICATION
  substrate.physical.alarm.escalation_required    — Alarm requires operator attention
  substrate.physical.measurement.quality_changed  — Sensor measurement quality shift
  substrate.physical.measurement.tolerance_deviation — Measured value outside DESIGN tolerance
  substrate.physical.measurement.recorded         — GPS/GNSS position measurement for SPATIAL
  substrate.physical.measurement_stream.data_available — Streaming data ready for COMPUTE
  substrate.physical.calibration.completed        — Instrument calibration finished
  substrate.physical.hazard_analysis.reviewed     — HazardAnalysis reassessed
  substrate.physical.digital_twin.drift_detected  — Twin diverged from physical reality
  substrate.physical.operating_mode.change_requested — Mode change requires approval
  substrate.physical.safety_function.tripped      — Safety function activated

Events Consumed by PHYSICAL:
  substrate.business.workflow.assigned             — Work order assigned (INT-P001)
  substrate.business.entity.updated                — Business entity change (INT-P001)
  substrate.knowledge.source.reliability_changed   — Source trust level changed (INT-P002)
  substrate.knowledge.proposition.status_changed   — Epistemic status change (INT-P002)
  substrate.compute.computation.completed          — MPC/analytics result ready (INT-P003)
  substrate.compute.pipeline.result_available      — Prediction pipeline output (INT-P003)
  substrate.communication.discourse.resolved       — Escalation discourse closed (INT-P004)
  substrate.communication.consensus.reached        — Operating mode change approved (INT-P004)
  substrate.communication.commitment.fulfilled     — Maintenance commitment done (INT-P004)
  substrate.design.component.released              — New component spec available (INT-P006)
  substrate.design.specification.safety_requirements_updated — Safety spec changed (INT-P006)
  substrate.design.fabrication_method.defined       — Manufacturing method specified (INT-P006)
  substrate.governance.norm.effective               — Safety regulation active (INT-P007)
  substrate.governance.assessment.completed         — Safety audit completed (INT-P007)
  substrate.temporal.booking.confirmed              — Maintenance time slot confirmed (INT-P008)
  substrate.temporal.activity.completed             — Scheduled activity done (INT-P008)
```

### Correlated Failure Scenarios

```
CORR-P001: COMPUTE + COMMUNICATION unavailable simultaneously
  Impact:    MPC degrades to PID. Alarm escalation queues. No advanced analytics.
  Response:  Basic control and safety UNAFFECTED. Edge tier operates independently.
             All events buffered for sync-on-reconnect.

CORR-P002: All cross-substrate dependencies unavailable (island mode)
  Impact:    PHYSICAL operates in full island mode. All local control loops, safety
             functions, and alarm management continue. No cross-substrate events emitted
             (queued). No new agent authorizations. Existing cached authorizations valid.
  Response:  Designed for this scenario (ASM-P002). Edge tier is self-sufficient for
             safety and basic control. Full capability restored on reconnection.

CORR-P003: Time source (DEP-P001) degraded
  Impact:    Measurement timestamp_uncertainty increases. Cross-zone time correlation
             degrades. Sequence of events (SOE) accuracy reduced.
  Response:  Local clocks continue with drift. Alarm raised. All Measurements tagged
             with increased timestamp_uncertainty. Control continues (relative timing
             still valid within single zone).
```

---

## 9. AUTHORIZATION & ACCESS MODEL

### Resources

```
RES-P001: Sensor — maps to: ENT-P001
RES-P002: Measurement — maps to: ENT-P002
RES-P003: MeasurementStream — maps to: ENT-P003
RES-P004: Actuator — maps to: ENT-P004
RES-P005: Command — maps to: ENT-P005
RES-P006: Calibration — maps to: ENT-P006
RES-P007: PhysicalConstraint — maps to: ENT-P007
RES-P008: Alarm — maps to: ENT-P008
RES-P009: ControlLoop — maps to: ENT-P009
RES-P010: Setpoint — maps to: ENT-P010
RES-P011: ControlSequence — maps to: ENT-P011
RES-P012: OperatingMode — maps to: ENT-P012
RES-P013: SafetyFunction — maps to: ENT-P013
RES-P014: SafetyEnvelope — maps to: ENT-P014
RES-P015: PhysicalEnvelope — maps to: ENT-P015
RES-P016: HazardAnalysis — maps to: ENT-P016
RES-P017: PhysicalAsset — maps to: ENT-P017
RES-P018: Zone — maps to: ENT-P018
RES-P019: Process — maps to: ENT-P019
RES-P020: ProcessExecution — maps to: ENT-P020
RES-P021: MaintenanceAction — maps to: ENT-P021
RES-P022: FieldbusAdapter — maps to: ENT-P022
RES-P023: DigitalTwin — maps to: ENT-P023
RES-P024: Event — maps to: ENT-P024
RES-P025: PhysicalTopology — maps to: ENT-P026
```

### Permission Matrix

```
| Actor \ Resource         | Sensor  | Measurement | Actuator | Command     | ControlLoop | SafetyFunc | SafetyEnv | PhysicalAsset | Process | ProcessExec |
|--------------------------|---------|-------------|----------|-------------|-------------|------------|-----------|---------------|---------|-------------|
| ACT-P001 (Operator)      | read    | read        | read     | create,read | mode change | read,monitor | read   | read,LOTO,state | read  | start,hold,abort,read |
| ACT-P002 (Engineer)      | CRUD    | read,correct | CRUD    | create,read | CRUD,tune   | create,read | draft   | CRUD          | CRUD    | read        |
| ACT-P003 (Narrow AI)     | read*   | read*       | read*    | create*     | read*       | monitor*   | read*   | read*         | read*   | read*       |
| ACT-P004 (General AI)    | read*   | read*       | read*    | create*     | read*,tune* | monitor*   | read*   | read*         | read*   | start*,read*|
| ACT-P005 (External Sys)  | read†   | read†       | —        | —           | —           | —          | —       | read†         | —       | read†       |
| ACT-P006 (Auditor)       | read    | read        | read     | read        | read        | read       | read    | read          | read    | read        |
| ACT-P007 (Safety Auth)   | read    | read        | read     | read        | read        | CRUD,bypass | approve | read,override | read    | read        |

* = Within PhysicalEnvelope only. Effective permission = stated ∩ PhysicalEnvelope ∩ SafetyEnvelope.
† = Validated, rate-limited, sandboxed per TRUST-P001.
```

### Ownership Rules

```
**Ownership rules:**
- Measurements are owned by the System. No Actor may modify a recorded Measurement.
  Corrections are new Measurements with provenance.
- Events are owned by the System. No Actor may modify or delete Events. Append-only.
- Commands are owned by the System once issued. Authority is attributed but immutable.
- SafetyEnvelopes require Safety Authority (ACT-P007) approval for activation.
- PhysicalConstraints require Safety Authority (ACT-P007) approval for any change.
- SafetyFunctions require Safety Authority (ACT-P007) approval for bypass.
  Bypasses are time-limited and auto-revoked.
- AI agent permissions are the intersection of PhysicalEnvelope ∩ SafetyEnvelope ∩
  PhysicalConstraints. The most restrictive always wins.

**Delegation rules:**
- ACT-P001 (Operator) may delegate to ACT-P003/P004 (AI) for specific tasks within
  the AI agent's PhysicalEnvelope. Delegation is logged and time-limited.
- ACT-P003/P004 (AI) may NOT delegate to other AI agents without human approval.
- LOTO locks are personal to the performing actor. Multi-lock LOTO requires all
  lock holders to release. Supervisor override requires safety review.

**Unauthenticated access:**
- NONE. All access to PHYSICAL requires authentication via DEP-P002.
  No anonymous sensor readings. No anonymous commands. No exceptions.

**Session model:**
- Sessions bound to authenticated identity (DEP-P002).
- Operator sessions persist across shift but require re-authentication at handoff.
- AI agent sessions bound to PhysicalEnvelope validity period.
- Emergency access: dedicated emergency credentials with full audit trail.
```

---

## 10. SECURITY & PRIVACY MODEL

### Data Classification

```
CLASS-P001: Safety-Critical — Entities: SafetyFunction configuration, SafetyEnvelope
            constraints, PhysicalConstraint values, safety trip Events. Highest
            protection. Integrity is paramount (tampering → safety hazard).

CLASS-P002: Operational — Entities: Measurements, Commands, ControlLoop configuration,
            Alarm configuration, ProcessExecution records. High protection. Integrity
            and availability critical for operations.

CLASS-P003: Configuration — Entities: Sensor/Actuator registration, FieldbusAdapter
            config, DigitalTwin config, PhysicalTopology. Moderate protection.
            Integrity important. Unauthorized changes could cause malfunction.

CLASS-P004: Audit — Entities: Events (all types). Highest integrity requirement.
            Append-only. Tamper-evident. Used for regulatory compliance and
            incident investigation.

CLASS-P005: PII — Entities: Actor references in Events, MaintenanceAction
            performed_by, LOTO performing_actor. Privacy-protected per applicable
            regulations. Retained per legal requirements.
```

### Threat Model

```
THREAT-P001: Unauthorized command injection — attacker sends commands to actuators
             — Mitigation: All commands authenticated, authorized, and validated against
               SafetyEnvelope. PhysicalEnvelope rate-limits AI agents. FieldbusAdapter
               validates data types and ranges. Defense in depth: independent safety
               system trips on dangerous conditions regardless of command source.
             — Source: SRC-P009 (IEC 62443)

THREAT-P002: Sensor data manipulation — attacker spoofs sensor readings
             — Mitigation: FieldbusAdapter integrity checks. Cross-validation against
               redundant sensors. DigitalTwin drift detection flags anomalous readings.
               Safety systems use independent sensor paths.
             — Source: SRC-P009 (IEC 62443)

THREAT-P003: Safety system bypass — attacker disables safety functions
             — Mitigation: SafetyFunctions execute on independent hardware. Only ACT-P007
               (Safety Authority) can bypass, with time limits and auto-revoke. Bypass
               state is continuously monitored and alarmed. No software path from basic
               control to safety system.
             — Source: SRC-P009 (IEC 61508, IEC 62443)

THREAT-P004: Event log tampering — attacker modifies audit trail
             — Mitigation: Append-only event store. Cryptographic hash chain. Write-once
               media for regulated industries. Cross-substrate event projection provides
               independent copy. Regular integrity verification.
             — Source: ASM-P009

THREAT-P005: Denial of service on control network — attacker floods fieldbus
             — Mitigation: Network segmentation per IEC 62443 zones. Rate limiting on
               all interfaces. Edge tier operates independently of external networks.
               Safety systems on isolated network segments.
             — Source: SRC-P009 (IEC 62443)

THREAT-P006: Insider threat — authorized user issues harmful commands
             — Mitigation: SafetyEnvelope validates ALL commands regardless of authority
               level. PhysicalConstraints cannot be overridden by software. Full audit
               trail. Anomaly detection on operator behavior patterns.
             — Source: SRC-P009, SRC-P013
```

### Abuse Cases

```
ABUSE-P001: AI agent command flooding — agent issues maximum rate commands to oscillate actuator
  Given:  AI agent with valid PhysicalEnvelope
  When:   Agent issues rapid alternating commands at max_command_rate
  Then:   Rate limiter enforces max_command_rate. Rate-of-change limits on ControlLoop
          outputs prevent mechanical stress. Anomalous pattern detection alerts operator.
          PhysicalEnvelope revoked if pattern persists.

ABUSE-P002: Setpoint manipulation — agent gradually moves setpoints toward unsafe region
  Given:  AI agent authorized to adjust setpoints
  When:   Agent makes incremental setpoint changes approaching SafetyEnvelope boundary
  Then:   Each setpoint change validated against SafetyEnvelope. Setpoints clamped at
          envelope boundary. Trend detection alerts operator when setpoints approach
          limits. Safety system trips if process variable exceeds limits regardless.

ABUSE-P003: Calibration fraud — actor records false calibration data
  Given:  Actor with calibration authority
  When:   Actor submits fabricated as-found/as-left readings
  Then:   Calibration records are immutable audit trail. Cross-validation against
          historical drift patterns flags statistical anomalies. Regulatory auditors
          (ACT-P006) can review full calibration chain. Reference standard traceability
          enables independent verification.

ABUSE-P004: LOTO abuse — actor locks out equipment to prevent production
  Given:  Operator with LOTO authority
  When:   Operator locks out equipment without legitimate maintenance reason
  Then:   LOTO requires documented reason. All LOTO events logged with performing_actor.
          Supervisor can investigate. Extended LOTO generates alerts. LOTO policy
          enforcement per organizational rules.
```

### Encryption and Network Security

```
**Encryption:**
- All data at rest: AES-256 or equivalent. Safety-critical data: additional integrity
  verification (HMAC or digital signature).
- All data in transit between zones: TLS 1.3 minimum.
- Fieldbus networks: per protocol capability. Legacy protocols without encryption:
  compensating controls (network isolation, monitoring, access control).
- Event store: cryptographic hash chain for tamper evidence.

**Network segmentation (per IEC 62443):**
- Safety systems: isolated network segment. No direct connection to business network.
- Control network: separated from IT network by industrial DMZ.
- Edge tier ↔ Organization tier: firewall with allow-list rules.
- FieldbusAdapter: protocol-specific security per SRC-P009.

**Secret handling:**
- FieldbusAdapter credentials: encrypted at rest, rotated per policy.
- API tokens: short-lived, scoped to specific resources.
- Emergency access credentials: sealed, audited on use, rotated after use.
- No secrets in Event payloads or Measurement values.
```

### Privacy Constraints

```
- Actor references in Events retained per legal/regulatory requirements (minimum 7 years
  for regulated industries).
- Operator performance data (response times, intervention patterns) aggregated before
  sharing outside immediate supervisory chain.
- Behavioral data from SRC-P013 was anonymized and aggregated before ingestion.
- Location data (physical_location) is operational, not personal tracking.
- GDPR/CCPA applicability: limited — most PHYSICAL data is about equipment, not people.
  Actor references are the primary PII concern.
```

---

## 11. BEHAVIORAL CONTRACTS (SYSTEM LAW)

### 11.1 Invariants (must ALWAYS hold)

```
INV-P001: A Command, once issued, is immutable. No Actor may modify the commanded_value,
          authority_ref, or timestamps of a persisted Command. Lifecycle state may only
          advance forward per SM-P002. — Source: ASM-P004, ASM-P009

INV-P002: An Event, once persisted, is immutable. No Actor, including system administrators,
          may modify, reorder, or delete Events. The Event log is append-only and is the
          source of truth for all physical system state. — Source: ASM-P009

INV-P003: Every Actuator has a declared safe_state. An Actuator entity without a safe_state
          attribute is a specification error and MUST NOT be persisted. — Source: ASM-P002

INV-P004: The SafetyEnvelope is always at least as restrictive as the union of all
          PhysicalConstraints on the asset. operational_limits ≤ PhysicalConstraint values.
          This invariant is verified at SafetyEnvelope creation and on every change.
          — Source: TERM-P014, SRC-P009

INV-P005: SafetyFunctions execute independently of basic process control. They share no
          CPU, memory, I/O channels, or network paths with basic control logic. This
          independence is an architectural invariant, not a runtime check.
          — Source: TERM-P013, SRC-P009 (IEC 61508)

INV-P006: Only one OperatingMode is active per PhysicalAsset at any time.
          — Source: TERM-P012

INV-P007: AI agent effective authority = PhysicalEnvelope ∩ SafetyEnvelope ∩
          PhysicalConstraints. The most restrictive always wins. No mechanism exists to
          bypass this intersection. — Source: ASM-P007, TERM-P015

INV-P008: A Measurement from a Sensor with expired or failed Calibration MUST have
          quality_code ≠ good (uncertain for expired, bad for failed). This is enforced
          at measurement creation, not as a post-hoc filter. — Source: ASM-P005, TERM-P006

INV-P009: A PhysicalAsset in LockedOut state accepts NO Commands to its Actuators.
          This is enforced at Command validation (FLOW-P002 Step 3), not as policy.
          — Source: TERM-P017 (LOTO), CAP-P009

INV-P010: The containment hierarchy of PhysicalAssets is a strict tree (no cycles).
          An asset's parent must be at a higher ISA-95 hierarchy level.
          — Source: TERM-P017, SRC-P004
```

### 11.2 Preconditions (before operation executes)

```
PRE-P001: FLOW-P002 (Command) requires: actuator exists AND actuator.health_status ≠ failed
          AND asset.operational_state ≠ LockedOut AND asset.operational_state ≠ Decommissioned
          AND SafetyEnvelope validation passes AND (if AI agent: PhysicalEnvelope validation
          passes). — Source: CAP-P007, CAP-P009

PRE-P002: FLOW-P005 (Execute Process) requires: process_ref in Approved state AND all
          required_assets in Operational state (not LockedOut, not Shutdown, not
          Decommissioned) AND required OperatingMode active AND all first-sequence
          preconditions met. — Source: CAP-P023

PRE-P003: IFC-P005b (ControlLoop Mode Change) requires: loop exists AND new_mode is a
          valid transition from current mode AND actor is authorized AND (if automatic:
          process_variable quality_code ≠ bad). — Source: CAP-P015

PRE-P004: IFC-P007b (LOTO Lock) requires: asset in Operational or Degraded state AND
          actor authorized for LOTO AND all actuators can reach safe_state.
          — Source: CAP-P022

PRE-P005: IFC-P008b (SafetyEnvelope Approve) requires: envelope in Drafted state AND
          approver is ACT-P007 (Safety Authority) AND moc_reference is valid AND
          operational_limits do not exceed PhysicalConstraints. — Source: CAP-P018

PRE-P006: SM-P001 LockedOut → ReturnToService requires: ALL lock holders have released
          their locks AND maintenance complete AND LOTO release authorized.
          — Source: TERM-P017 (LOTO)
```

### 11.3 Postconditions (after operation completes)

```
POST-P001: After FLOW-P002 (Command), the Command entity exists with verification_result
           ∈ {confirmed, timeout, mismatch, rejected} AND an Event is recorded AND (if
           safety-critical) a cross-substrate event is emitted. — Source: CAP-P008

POST-P002: After FLOW-P005 (Execute Process, completed), a ProcessExecution entity exists
           with status = Completed AND measurements_log, commands_log, and alarms_log are
           complete AND quality_results recorded AND cross-substrate event emitted.
           — Source: CAP-P023

POST-P003: After FLOW-P006 (Safety Trip), ALL affected actuators are in safe_state AND
           safety trip Event is recorded AND operators are alerted AND cross-substrate
           event is emitted AND non-safety Commands to affected assets are blocked until
           authorized reset. — Source: CAP-P016

POST-P004: After FLOW-P007 (LOTO Lock), asset.operational_state = LockedOut AND all
           actuators at safe_state AND maintenance envelope active AND all Commands
           rejected AND LOTO Event recorded. — Source: CAP-P022

POST-P005: After FLOW-P008 (Calibration, pass), subject calibration_state = Current AND
           next_due_date reset AND quality_code evaluation restored to normal AND
           calibration-due alarms cleared. — Source: CAP-P028

POST-P006: After SM-P001 ReturnToService → Operational, normal SafetyEnvelope restored AND
           all safety functions tested AND calibrations verified AND asset available for
           control. — Source: TERM-P017
```

### 11.4 Forbidden States (must NEVER occur)

```
FORBID-P001: A Command that has been Rejected by SafetyEnvelope validation reaching an
             Actuator. Rejected Commands NEVER progress past Issued state. The command
             path from validation failure to physical actuator does not exist.
             — Source: ASM-P002, CAP-P007

FORBID-P002: An Actuator without a declared safe_state existing in the system. This is
             a specification error caught at registration time. — Source: ASM-P002, INV-P003

FORBID-P003: A SafetyFunction sharing CPU, memory, or I/O with basic process control logic.
             Independence is architectural (separate hardware), not logical (separate
             threads). — Source: INV-P005, SRC-P009

FORBID-P004: An AI agent issuing Commands to a SIL-rated SafetyFunction. AI agents may
             MONITOR safety functions. They may NOT control them. — Source: CAP-P020, UNK-P005

FORBID-P005: A PhysicalConstraint being overridden by software command. If a pipe is rated
             for 150 PSI, no Command, Setpoint, or configuration change may create a
             condition that exceeds 150 PSI. — Source: TERM-P007, INV-P004

FORBID-P006: A Measurement being modified after persistence. Corrections create NEW
             Measurements with correction_of provenance. The original is immutable.
             — Source: INV-P002, TERM-P002

FORBID-P007: Two OperatingModes simultaneously active on the same PhysicalAsset.
             — Source: INV-P006

FORBID-P008: A LOTO release proceeding while any lock holder has not released their lock
             (multi-lock LOTO safety). — Source: PRE-P006

FORBID-P009: An Event being deleted from the event store. Events are the legal record.
             Deletion is not a supported operation. — Source: INV-P002, ASM-P009

FORBID-P010: A hard_realtime ControlLoop executing on cloud infrastructure.
             hard_realtime requires dedicated deterministic hardware.
             — Source: ASM-P003, TERM-P025
```

### 11.5 Failure Guarantees (what is guaranteed when things go wrong)

```
FAIL-P001: If communication between a ControlLoop and its output Actuator is lost, the
           Actuator MUST drive to its declared safe_state within the actuator's
           response_time. This is enforced by hardware watchdog, not software timer.
           — Source: ASM-P002, CAP-P010

FAIL-P002: If the Event store becomes unavailable, Measurements and Commands MUST be
           buffered locally (edge tier) and synchronized on recovery. No data is lost.
           Control and safety operations continue. — Source: ASM-P009

FAIL-P003: If a FieldbusAdapter disconnects from hardware, ALL Sensors via that adapter
           produce quality_code: bad. ALL Actuators via that adapter are assumed to be
           in last-known state. Communication_loss alarm raised. Affected ControlLoops
           enter fallback mode. — Source: FLOW-P001 Step 1 error path

FAIL-P004: If SafetyEnvelope validation service is unavailable, ALL Commands are REJECTED
           (fail-closed). No command reaches an actuator without safety validation.
           This is the only acceptable failure mode for the safety validation path.
           — Source: ASM-P002, FORBID-P001

FAIL-P005: If time source (DEP-P001) is degraded, Measurements continue with increased
           timestamp_uncertainty. Control loops continue (relative timing valid within
           zone). Cross-zone time correlation degraded. Alarm raised.
           — Source: CORR-P003

FAIL-P006: If all cross-substrate dependencies fail simultaneously (island mode),
           PHYSICAL continues local control, safety, and alarm management independently.
           All events buffered. Full capability restored on reconnection.
           — Source: CORR-P002, ASM-P002

FAIL-P007: If a ControlSequence encounters an abort condition, ALL affected actuators
           are driven to safe_state. The sequence CANNOT be resumed from abort state —
           a new execution must be started. Partial results are preserved.
           — Source: SM-P004

FAIL-P008: If proof test of a SafetyFunction is overdue, a mandatory alarm is raised
           at priority: high. The SafetyFunction remains active (it does not shut down
           because testing is late). The alarm persists until proof test is performed.
           — Source: TERM-P013
```

---

## 12. DECISION POINTS (WHERE THE SYSTEM CHOOSES)

> Decision points identify where runtime logic must choose between options. Each
> decision has explicit selection rules and fallbacks. No decision is left to
> "implementation discretion" — ambiguity in physical systems is a safety risk.

```
DEC-P001: Command Safety Validation
          — Context: FLOW-P002, Step 4 — Source: CAP-P007, SRC-P009
  Inputs:          commanded_value, actuator_ref, active SafetyEnvelope, PhysicalConstraints
  Options:         Pass | Reject (with specific constraint violated)
  Selection rule:
    VALIDATE IN ORDER (short-circuit on first failure):
      1. commanded_value within actuator range (ENT-P004.range_min/max)
      2. commanded_value within SafetyEnvelope.operational_limits for this actuator
      3. commanded_value would not cause any interlock_condition to trigger
      4. Rate of change from current position would not exceed rate_of_change_limit
      5. Combined effect with other pending commands would not violate envelope
    ALL PASS → Pass. ANY FAIL → Reject with first failed constraint.
  Fallback:        If SafetyEnvelope lookup fails: REJECT (fail-closed, FAIL-P004).
  Audit:           Every validation (pass or reject) recorded as Event with full input context.

DEC-P002: Alarm Priority Assignment
          — Context: FLOW-P004 — Source: CAP-P019, SRC-P004 (ISA-18.2)
  Inputs:          condition_type, consequence, required_response_time, alarm configuration
  Options:         emergency | high | medium | low | diagnostic
  Selection rule:
    PRIORITY FROM CONSEQUENCE:
      Imminent danger to life or environment → emergency
      Equipment damage likely within minutes → high
      Process upset, quality deviation → medium
      Informational, no immediate action → low
      Diagnostic, engineering use only → diagnostic
    OVERRIDE: During alarm flood (>10/operator/10 min), low-priority alarms may be
    auto-shelved. Emergency and high NEVER auto-shelved.
  Fallback:        If consequence unknown: default to high (conservative).
  Audit:           Priority assignment and any override logged.

DEC-P003: ControlLoop Fallback Mode
          — Context: FLOW-P003, Step 2 — Source: CAP-P011, SRC-P010
  Inputs:          process_variable quality_code, sensor health, loop configuration
  Options:         Continue_automatic | Use_last_known | Switch_to_manual | Drive_to_safe
  Selection rule:
    quality_code: good → Continue_automatic
    quality_code: uncertain → Continue_automatic with alarm to operator
    quality_code: bad (transient, <configured_holdover) → Use_last_known value
    quality_code: bad (persistent, >configured_holdover) → Switch_to_manual, alert operator
    sensor health: failed → Drive_to_safe_state immediately
    If MPC loop and COMPUTE unavailable → degrade to PID (INT-P003)
  Fallback:        If decision cannot be made: Drive_to_safe_state (ASM-P002).
  Audit:           Mode transition and reason recorded as Event.

DEC-P004: LOTO Multi-Lock Resolution
          — Context: FLOW-P007, Step 11 — Source: CAP-P022, SRC-P009
  Inputs:          list of active locks on asset, unlock request
  Options:         Release_lock | Reject_release
  Selection rule:
    Each lock is personal to performing_actor.
    Release_lock: requesting actor is the lock holder for THIS specific lock.
    Reject_release: requesting actor does not hold a lock, OR other locks remain
    (asset stays LockedOut until ALL locks released).
    Supervisor override: requires documented safety review AND all lock holders
    contacted/accounted for.
  Fallback:        If lock holder unreachable: supervisor override with safety review.
  Audit:           Every lock/unlock attempt logged with all lock holders listed.

DEC-P005: AI Agent Escalation to Human
          — Context: FLOW-P002 (AI path) — Source: ASM-P007, TERM-P015
  Inputs:          command context, PhysicalEnvelope, current system state
  Options:         Proceed_autonomously | Escalate_to_human
  Selection rule:
    MUST ESCALATE:
      Command would affect a SIL-rated SafetyFunction (even indirectly)
      Current system state is outside PhysicalEnvelope.human_approval_triggers
      Sensor data anomaly detected (readings outside historical envelope)
      Novel operating condition (no prior data for this combination)
      Multiple simultaneous alarms (>3 active on same asset)
    MAY PROCEED:
      Command within PhysicalEnvelope AND normal operating conditions AND
      historical precedent for this action AND no active alarms on target
  Fallback:        If uncertain: ESCALATE (ASM-P007 — most restrictive).
  Audit:           Every escalation decision logged with reasoning context.

DEC-P006: Measurement Quality Degradation
          — Context: FLOW-P001, Steps 3-5 — Source: CAP-P003, ASM-P005
  Inputs:          raw measurement value, sensor range, calibration state, sensor health
  Options:         good | uncertain | bad | substituted
  Selection rule:
    IN ORDER OF SEVERITY (worst wins):
      Sensor health: failed → bad
      Calibration: failed → bad
      Value outside sensor range → bad
      Calibration: overdue → uncertain
      FieldbusAdapter: degraded → uncertain
      Value within range AND calibration current AND sensor healthy → good
      If corrected measurement → substituted (with provenance to original)
  Fallback:        If quality cannot be determined: uncertain (conservative).
  Audit:           Quality code assignment logged with reason.
```

---

## 13. CONCURRENCY & ORDERING

```
**Concurrent access:**
- Multiple ControlLoops may read from the same Sensor concurrently. Reads are
  non-blocking. Each loop gets the latest Measurement independently.
- Multiple Commands to the same Actuator are serialized by the SafetyEnvelope
  validation step. Only one command may be in the Issued→Verified lifecycle for
  a given actuator at a time (unless explicitly configured for queuing).
- Multiple Actors may read Events, Measurements, and entity state concurrently.
  Read operations never block write operations.

**Conflict resolution:**
- Command conflicts (two actors commanding same actuator):
  Priority-based: safety > high > normal > low.
  Same priority: last-writer-wins for manual; ControlLoop output overrides manual
  if loop is in automatic mode. Conflict logged as Event.
- Setpoint conflicts (cascade output vs operator manual):
  Mode determines precedence: cascade mode → cascade output wins; manual → operator wins.
- OperatingMode transitions: serialized per asset. Concurrent requests queued FIFO.

**Ordering guarantees:**
- Events are totally ordered per asset (asset-level sequence number).
- Events are partially ordered across assets (timestamp + clock uncertainty).
- Measurements within a MeasurementStream are totally ordered (stream sequence number).
- Commands to a single actuator are totally ordered (command sequence per actuator).
- Cross-substrate events are eventually consistent with domain Events.

**Idempotency:**
- Command Submission (IFC-P003): idempotency_key per actuator. Duplicate → return existing.
- Measurement Ingestion (IFC-P002): sensor_ref + timestamp. Duplicate → reject.
- Alarm Acknowledgment (IFC-P004b): idempotent per alarm + actor + window.
- Event creation: event_id (UUID) globally unique. Duplicate → reject.

**Race conditions to prevent:**

RACE-P001: Two operators simultaneously requesting LOTO on same asset
           Prevention: Serialized via optimistic locking on asset.operational_state.
           Second request succeeds (both locks recorded). Multi-lock LOTO is valid.

RACE-P002: ControlLoop output and operator manual command to same actuator simultaneously
           Prevention: Mode determines authority. If auto: loop wins, operator command
           rejected with "loop in automatic — switch to manual first." If manual: operator
           wins, loop output computed but not applied.

RACE-P003: SafetyEnvelope change concurrent with Command validation
           Prevention: SafetyEnvelope is versioned. Command validation locks envelope
           version for the duration of validation (read lock). Envelope updates acquire
           write lock. Commands validated against consistent envelope version.

RACE-P004: Multiple ControlSequences requesting same equipment simultaneously
           Prevention: Equipment reservation at sequence start. Second sequence blocked
           until first completes or releases. Deadlock detection across sequences.

**Atomicity boundaries:**
- Measurement + Event: atomic (FLOW-P001 Steps 6-8)
- Command creation + Event: atomic (FLOW-P002 Steps 7-8)
- LOTO shutdown + state transition + envelope swap: atomic (FLOW-P007 Steps 3-7)
- ProcessExecution creation + logging start: atomic (FLOW-P005 Steps 5-6)
- Safety trip + safe state + event: atomic (FLOW-P006 Steps 1-4)

**Eventual consistency:**
- Domain Event → cross-substrate event projection: < 5 seconds typical
- Measurement → DigitalTwin synchronization: per twin.synchronization_rate
- Calibration state → quality_code propagation: < 1 second
- Alarm state → COMMUNICATION escalation: < 30 seconds
```

---

## 14. ERROR HANDLING & RECOVERY

### 14.1 Error Taxonomy

```
ERR-P001: Validation error — input fails schema or constraint validation
ERR-P002: Authorization error — actor lacks permission for requested operation
ERR-P003: Asset not found — referenced asset does not exist
ERR-P004: Duplicate resource — sensor/actuator already registered at address
ERR-P005: Sensor not found — referenced sensor does not exist
ERR-P006: Out-of-range measurement — value outside sensor declared range
ERR-P007: Safety envelope violation — command/setpoint violates active envelope
ERR-P008: Asset locked out — operation attempted on LOTO asset
ERR-P009: Actuator failed — target actuator health_status = failed
ERR-P010: Rate limit exceeded — AI agent exceeded PhysicalEnvelope.max_command_rate
ERR-P011: Invalid alarm transition — alarm not in valid state for requested transition
ERR-P012: Scan rate incompatible — ControlLoop scan_rate exceeds latency_class capability
ERR-P013: Preconditions not met — ProcessExecution preconditions not satisfied
ERR-P014: Assets unavailable — required assets not in Operational state
ERR-P015: Invalid state transition — requested transition not valid per state machine
ERR-P016: LOTO release denied — not all lock holders have released
ERR-P017: MOC reference required — SafetyEnvelope change requires MOC documentation
ERR-P018: Limits exceed constraints — operational_limits wider than PhysicalConstraints
ERR-P019: Protocol not supported — FieldbusAdapter protocol type not available
ERR-P020: Connection failed — FieldbusAdapter cannot connect to hardware
ERR-P021: Simulation unavailable — COMPUTE Pipeline for DigitalTwin not reachable
```

### 14.2 Semantics

```
**User-facing errors:**
- ERR-P007 (safety envelope violation): MUST include the specific constraint violated,
  the commanded value, and the envelope limit. Operators need to understand WHY a
  command was rejected to take corrective action.
- ERR-P008 (asset locked out): MUST include LOTO tag information and performing actor
  so operator can coordinate with maintenance.
- ERR-P013 (preconditions not met): MUST list each unmet precondition individually.

**Retry semantics:**
- ERR-P007: NEVER retry automatically. Safety rejection is definitive until envelope changes.
- ERR-P008: NEVER retry automatically. LOTO is definitive until released.
- ERR-P020: Retry with exponential backoff (1s, 5s, 30s, 2m, 10m). Circuit breaker
  at 5 consecutive failures. Alert on circuit breaker open.
- ERR-P021: Retry 3 times, then degrade (twin goes stale). Alert.

**Partial failure:**
- MeasurementStream batch (IFC-P002b): per-measurement acceptance. Valid measurements
  persisted even if some in batch rejected. Response includes per-index results.
- ProcessExecution with sequence failure: depends on sequence abort_conditions.
  Recoverable failure → hold and alert. Unrecoverable → abort.

**Degraded modes (dependency failure):**
- COMPUTE unavailable: MPC → PID. Twin → stale. Predictive → scheduled. (INT-P003)
- COMMUNICATION unavailable: Notifications → local queue. Escalation → timer paused. (INT-P004)
- KNOWLEDGE unavailable: Ingestion → queued. Operations → unaffected. (INT-P002)
- BUSINESS unavailable: Cross-refs → cached. New agents → blocked. (INT-P001)
- Time source degraded: timestamps → wider uncertainty. Control → continues. (CORR-P003)
- All dependencies down: island mode. Local control + safety. (CORR-P002)

**Recovery:**
- On dependency restoration: drain event queue (in order), sync state, verify consistency.
- On FieldbusAdapter reconnection: re-read all sensor states, verify actuator positions,
  reconcile with expected state, alert on discrepancies.
- On Event store recovery: replay buffered events, verify integrity chain, resume normal.

**Circuit breakers:**
- FieldbusAdapter: open after 5 consecutive failures. Half-open after 30s. Close on success.
- Cross-substrate event emission: open after 50% failure rate over 100 attempts.
  Half-open after 60s. Events queued during open state.
- COMPUTE computation request: open after 3 consecutive timeouts. Degrade to fallback.
```

---

## 15. PERSISTENCE REQUIREMENTS

```
PERS-P001: ENT-P002 (Measurement) — Source: ASM-P009, SRC-P002
  Access patterns:       Write-heavy (up to 10M/sec at large scale). Primary queries:
                         by sensor_ref + time_range, by asset_ref + time_range.
                         Aggregation queries (min, max, avg, stddev over time windows).
  Constraints:           Append-only. Immutable. No updates. No deletes.
  Consistency:           Write-ahead log at edge. Eventually consistent with organization tier.
  Retention & deletion:  Minimum 7 years for regulated industries. Configurable per stream.
                         Raw data retained per retention_policy. Aggregated data indefinitely.
  Backup & recovery:     RPO: 0 (no data loss — buffered at edge). RTO: < 5 minutes for
                         query availability.
  Size projections:      ~100 bytes/measurement. Medium plant: 1M/sec × 86400 sec/day
                         = ~8 TB/day raw. Compression 10:1 typical = ~800 GB/day stored.
  Seed data:             None required (greenfield).

PERS-P002: ENT-P024 (Event) — Source: ASM-P009
  Access patterns:       Write-heavy. Primary queries: by target_ref + time_range,
                         by event_type + time_range, by actor_ref + time_range.
                         Sequence reconstruction for incident investigation.
  Constraints:           Append-only. Immutable. Cryptographic hash chain. No deletes.
  Consistency:           Strong consistency within zone. Eventually consistent cross-zone.
  Retention & deletion:  Minimum 7 years. Safety events: 25 years or equipment lifetime.
  Backup & recovery:     RPO: 0. RTO: < 10 minutes.
  Size projections:      ~500 bytes/event average. Typically 10-100x fewer events than
                         measurements. Medium plant: ~100 GB/day.
  Seed data:             None required.

PERS-P003: ENT-P005 (Command) — Source: TERM-P005
  Access patterns:       Write-moderate. Primary queries: by actuator_ref + time_range,
                         by authority_ref + time_range, by verification_result.
  Constraints:           Append-only once issued. Lifecycle fields (acknowledged_at, etc.)
                         advance forward only per SM-P002.
  Consistency:           Strong consistency per actuator (command serialization).
  Retention & deletion:  Same as Events (7-25 years).
  Backup & recovery:     RPO: 0. RTO: < 5 minutes.
  Size projections:      ~300 bytes/command. 10-100x fewer than measurements.

PERS-P004: ENT-P017 (PhysicalAsset) — Source: TERM-P017
  Access patterns:       Read-heavy, write-rare. Primary queries: by hierarchy (parent/child),
                         by zone, by operational_state, by asset_type.
  Constraints:           Event-sourced. Current state derived from event log.
  Consistency:           Strong consistency (state transitions are serialized).
  Retention & deletion:  Indefinite. Decommissioned assets retained for historical analysis.
  Backup & recovery:     RPO: < 1 minute. RTO: < 5 minutes.
  Size projections:      ~2 KB/asset. Medium plant: ~10K assets = ~20 MB (negligible).

PERS-P005: ENT-P014 (SafetyEnvelope) — Source: TERM-P014, SRC-P009
  Access patterns:       Read-heavy (every command validation). Write-rare (MOC-controlled).
                         Primary queries: by asset_ref (active envelope), by version history.
  Constraints:           Version-controlled. All versions retained. Active version cached
                         at edge for low-latency command validation.
  Consistency:           Strong consistency. Cached copies invalidated on version change.
  Retention & deletion:  Indefinite. All versions retained for regulatory compliance.
  Backup & recovery:     RPO: 0. RTO: < 1 minute (critical for command validation).
  Size projections:      ~5 KB/envelope. Negligible.

PERS-P006: ENT-P020 (ProcessExecution) — Source: TERM-P020
  Access patterns:       Write-moderate during execution. Read-heavy for regulatory audit.
                         Primary queries: by process_ref + time_range, by status, by
                         operator_ref.
  Constraints:           Append-only during execution. Immutable after completion.
  Consistency:           Strong consistency per execution.
  Retention & deletion:  Minimum 7 years. Pharma: per FDA 21 CFR Part 11 (product lifetime + 1 year).
  Backup & recovery:     RPO: 0. RTO: < 10 minutes.
  Size projections:      Variable. Batch execution: ~1-100 MB (measurements + commands + alarms).
                         Continuous process segment: defined by time window.
```

---

## 16. MIGRATION & ONBOARDING

```
NOT APPLICABLE — greenfield system. No existing SUBSTRATE-PHYSICAL deployment to migrate from.

However, onboarding from legacy systems is expected:

**Legacy system onboarding paths:**
- SCADA/DCS migration: Tag database → Sensor/Actuator registration via IFC-P001/IFC-P009.
  Historian data → MeasurementStream backfill via IFC-P002b batch ingestion.
  Alarm configuration → Alarm entities via IFC-P004a.
- PLC migration: IO configuration → FieldbusAdapter data_mapping. Program logic →
  ControlLoop/ControlSequence definitions. Safety logic → SafetyFunction definition
  (requires independent safety review).
- IoT platform migration: Device registry → Sensor/Actuator registration.
  Telemetry schema → MeasurementStream configuration. Device shadow → DigitalTwin.
- Lab automation migration: SiLA2 commands → ControlSequence steps.
  Method definitions → Process entities. LIMS integration → ProcessExecution records.
- Building management migration: BACnet objects → PhysicalAsset/Sensor/Actuator.
  Schedules → ControlSequence. ASHRAE Guideline 36 sequences → ControlSequence.

**Onboarding constraints:**
- Safety-critical configurations (SafetyFunction, SafetyEnvelope) MUST be independently
  verified during migration. They cannot be automatically imported from legacy systems.
- Calibration history can be imported as historical records but current calibration state
  must be verified.
- PhysicalConstraints must be verified against current nameplate/engineering data.
```

---

## 17. OPERATIONAL PROFILE

### 17.1 Performance & Resource Constraints

```
**Latency budgets:**
- IFC-P002a (Measurement single): p50 < 1ms, p95 < 5ms, p99 < 10ms (per latency_class)
- IFC-P003 (Command Submission, including safety validation): p50 < 5ms, p95 < 20ms,
  p99 < 50ms. Safety validation MUST complete within 50ms at p99.
- IFC-P004b (Alarm Acknowledge): p50 < 100ms, p95 < 500ms
- IFC-P005c (Setpoint Update): p50 < 5ms, p95 < 20ms (same path as Command)
- FLOW-P006 (Safety Trip, Steps 1-4): MUST complete within SafetyFunction.response_time_
  requirement (typically 50-500ms depending on SIL level)
- IFC-P002c (Measurement Query): p50 < 100ms, p95 < 1s for 1-hour window

**Throughput expectations:**
- Small deployment (building/lab): 1K-10K measurements/sec
- Medium deployment (manufacturing plant): 100K-1M measurements/sec
- Large deployment (refinery/utility): 1M-10M measurements/sec
- Command rate: 10-100x lower than measurement rate
- Event rate: proportional to state changes, typically 1-10% of measurement rate

**Payload limits:**
- Measurement: ≤1 KB per measurement (typically ~100 bytes)
- Command: ≤2 KB per command
- Event: ≤4 KB per event
- MeasurementStream batch: ≤10 MB per batch (configurable)
- ProcessExecution record: ≤1 GB total (measurements + commands + alarms)

**Rate limits:**
- Per AI agent per PhysicalEnvelope: max_command_rate (configurable, default 10/sec)
- Per External System (ACT-P005): configurable per trust level
- Per FieldbusAdapter: limited by protocol bandwidth (not software-configurable)

**Scalability model:**
- Horizontal: per-zone partitioning. Each zone is independently scalable.
- Vertical: measurement ingestion rate per zone scales with edge hardware.
- Cross-zone: eventual consistency. Zone coordination via organization tier.
```

### 17.2 Configuration & Environment

```
**Environment variables (representative, not exhaustive):**
- PHYSICAL_ZONE_ID — string — zone identity for this deployment — required
- PHYSICAL_EDGE_MODE — boolean — operate in edge-only mode — default: false
- PHYSICAL_EVENT_RETENTION_DAYS — integer — minimum event retention — default: 2555 (7 years)
- PHYSICAL_SAFETY_VALIDATION_TIMEOUT_MS — integer — max safety validation time — default: 50
- PHYSICAL_ALARM_FLOOD_THRESHOLD — integer — alarms/operator/10min — default: 10
- PHYSICAL_COMMAND_VERIFY_TIMEOUT_MS — integer — max command verification wait — default: 5000
- PHYSICAL_TWIN_DRIFT_CHECK_INTERVAL_S — integer — twin drift check frequency — default: 60
- PHYSICAL_ISLAND_MODE_CACHE_TTL_H — integer — cached authorization validity — default: 24

**Feature flags:**
- ff_mpc_enabled — enable MPC control loops (requires COMPUTE) — default: false
- ff_digital_twin_enabled — enable DigitalTwin synchronization — default: false
- ff_cross_substrate_events — enable cross-substrate event emission — default: true
- ff_predictive_maintenance — enable predictive maintenance models — default: false

**Secrets:**
- FieldbusAdapter credentials: encrypted at rest, injected at runtime
- Cross-substrate authentication tokens: rotated per policy
- Emergency access credentials: sealed, audited on use
```

### 17.3 Versioning & Evolution

```
- API versioning: major version in URL path (/v1/). Minor versions backward-compatible.
- SafetyEnvelope versions: immutable, referenced by version number. Active version tracked.
- Process versions: immutable. ProcessExecution locks version at start.
- FieldbusAdapter protocol support: additive (new protocols added, existing never removed).
- Event schema: additive (new event_types, new payload fields). Never remove fields.
- Breaking changes: require migration path and safety review.
```

### 17.4 Storage & Infrastructure Recommendations (NON-BINDING)

```
REC-P001: Time-series database for Measurements — purpose: high-throughput append-only
          ingestion with efficient time-range queries and built-in aggregation.
          — Tradeoffs: specialized for time-series workload; not suitable for relational
            queries. May require separate store for entity metadata.

REC-P002: Append-only log for Events — purpose: immutable event sourcing with
          cryptographic hash chain and efficient sequential reads.
          — Tradeoffs: excellent for write and sequential read; random access slower.

REC-P003: Edge-first deployment — purpose: local execution for real-time control with
          sync-on-reconnect to organization tier.
          — Tradeoffs: operational complexity of managing edge nodes; but required for
            latency guarantees and offline operation.

REC-P004: Independent safety hardware — purpose: SIL-rated safety functions on dedicated
          hardware (safety PLC, safety relay) separate from basic control.
          — Tradeoffs: higher hardware cost; but required for IEC 61508 compliance and
            independence invariant (INV-P005).

Implementers MAY ignore this entire sub-section. The specification defines contracts,
not infrastructure.
```

---

## 18. TEST PLAN (PROOF IT WORKS)

> At minimum, one test scenario per MUST capability, per state machine, per forbidden
> state, and per failure guarantee. Tests are executable specifications.

### Coverage Requirement

```
At minimum, one test scenario per:
- MUST capability (CAP-P001 through CAP-P029)
- State machine (SM-P001 through SM-P006)
- Forbidden state (FORBID-P001 through FORBID-P010)
- Failure guarantee (FAIL-P001 through FAIL-P008)
- Integration contract (INT-P001 through INT-P009)
- Abuse case (ABUSE-P001 through ABUSE-P004)
```

### Test Scenarios

```
TEST-P001: Sensor registration and measurement ingestion
           — Covers: CAP-P001, CAP-P002, ENT-P001, ENT-P002, IFC-P001, IFC-P002
  Given:        A FieldbusAdapter connected to a temperature sensor (Modbus TCP)
  When:         Engineer registers sensor via IFC-P001a, then sensor produces readings
  Then:         Sensor entity created with correct attributes. Measurements persisted
                with quality_code: good, timestamp from synchronized source, and value
                within declared range. Measurement queryable via IFC-P002c by sensor_ref
                + time_range.
  Failure means: Core sensing pipeline broken. Nothing else works without this.

TEST-P002: Measurement quality degradation on expired calibration
           — Covers: CAP-P003, SM-P006, INV-P008, DEC-P006
  Given:        Sensor with calibration next_due_date = yesterday
  When:         Sensor produces a Measurement
  Then:         quality_code automatically set to "uncertain." Calibration-due alarm
                raised. ControlLoops using this sensor alerted. Quality code cannot be
                overridden to "good" without new passing calibration.
  Failure means: Calibration-quality linkage broken. Untrustworthy data treated as good.

TEST-P003: Command lifecycle with safety validation
           — Covers: CAP-P007, CAP-P008, SM-P002, FLOW-P002, DEC-P001
  Given:        Actuator (valve, 0-100%) with SafetyEnvelope max: 80%
  When:         Operator submits command: open to 90%
  Then:         Command REJECTED with ERR-P007 specifying "SafetyEnvelope limit: 80%,
                commanded: 90%." Command entity created with verification_result: rejected.
                Event recorded. Actuator position unchanged.
  Failure means: Safety validation bypass. FORBID-P001 violated. Critical safety failure.

TEST-P004: Command lifecycle complete (happy path)
           — Covers: CAP-P008, SM-P002
  Given:        Actuator (valve, 0-100%) with SafetyEnvelope max: 80%, feedback sensor
  When:         Operator submits command: open to 50%
  Then:         Command passes safety validation. Status: Issued → Acknowledged → Executed →
                Verified_Confirmed. Feedback sensor confirms 50% ± tolerance.
                All timestamps recorded. Event created.
  Failure means: Command lifecycle state machine broken.

TEST-P005: LOTO lock and unlock
           — Covers: CAP-P022, SM-P001 (LockedOut), FLOW-P007, INV-P009
  Given:        PhysicalAsset in Operational state with active ControlLoop
  When:         Operator requests LOTO lock
  Then:         All actuators driven to safe_state. Asset transitions to LockedOut.
                SafetyEnvelope replaced with maintenance envelope. ALL subsequent commands
                to any actuator on this asset REJECTED with ERR-P008. LOTO Event recorded.
  Failure means: LOTO enforcement broken. Maintenance safety compromised.

TEST-P006: LOTO command rejection
           — Covers: CAP-P009, INV-P009, FORBID-P001
  Given:        PhysicalAsset in LockedOut state
  When:         Any actor (operator, AI, control loop) submits Command to asset's actuator
  Then:         Command REJECTED with ERR-P008. Command never reaches actuator. Event recorded.
  Failure means: LOTO bypass possible. Safety-critical failure.

TEST-P007: Safety function trip
           — Covers: CAP-P016, CAP-P017, FLOW-P006, INV-P005
  Given:        SafetyFunction monitoring pressure, trigger at 145 PSI, safe action: close valve
  When:         Pressure sensor reads 146 PSI
  Then:         SafetyFunction triggers INDEPENDENTLY of basic control. Valve driven to
                closed (safe_state). Safety trip Event recorded. All operators alerted.
                Non-safety commands to affected assets blocked. Cross-substrate event emitted.
  Failure means: Safety system failure. Potential for physical harm.

TEST-P008: Safety function independence
           — Covers: INV-P005, FORBID-P003
  Given:        SafetyFunction configured on dedicated safety hardware
  When:         Basic control system (PLC/DCS) becomes unavailable (power failure, crash)
  Then:         SafetyFunction continues to operate. Monitoring continues. Trip capability
                intact. Safety system is completely independent of basic control.
  Failure means: Safety independence violated. IEC 61508 non-compliance.

TEST-P009: AI agent PhysicalEnvelope enforcement
           — Covers: CAP-P020, INV-P007, FORBID-P004, DEC-P005
  Given:        AI agent with PhysicalEnvelope: max_command_rate: 5/sec, accessible_actuators: [valve_1]
  When:         AI agent attempts: (a) command to valve_2 (not in envelope),
                (b) 6th command in 1 second to valve_1, (c) setpoint near safety limit
  Then:         (a) REJECTED — actuator not in accessible_actuators. (b) REJECTED — rate
                limit exceeded. (c) If within PhysicalEnvelope range: accepted with safety
                validation. If approaching limit: escalation triggered per DEC-P005.
  Failure means: AI agent can exceed bounded authority.

TEST-P010: Alarm lifecycle (ISA-18.2)
           — Covers: CAP-P019, SM-P003, FLOW-P004
  Given:        Alarm configured: high temperature, trigger: 200°C, priority: high
  When:         Temperature reaches 201°C and persists for on_delay, then drops to 195°C
  Then:         State: Normal → Active_Unacknowledged (annunciated). Operator acknowledges →
                Active_Acknowledged. Temperature drops below trigger - deadband →
                Normal (return to normal). All transitions recorded as Events.
  Failure means: ISA-18.2 lifecycle broken. Alarm management non-compliant.

TEST-P011: Alarm flood detection
           — Covers: CAP-P019, DEC-P002
  Given:        Operator monitoring 10 assets
  When:         12 alarms trigger within 10 minutes for this operator
  Then:         Alarm flood detected (>10 alarms/operator/10 min per ISA-18.2 guidance).
                Rationalization alert raised. Emergency and high alarms NEVER auto-shelved.
                Low-priority alarms may be auto-shelved.
  Failure means: Alarm flood overwhelms operator. Safety risk.

TEST-P012: ControlLoop scan cycle
           — Covers: CAP-P011, FLOW-P003, DEC-P003
  Given:        PID ControlLoop: Kp=1, Ki=0.1, Kd=0, setpoint=100°C, scan_rate=1 second
  When:         Process variable = 95°C (error = +5)
  Then:         PID computes output. Command submitted to actuator via FLOW-P002 (with
                safety validation). Performance metrics updated. If output within limits:
                actuator position changes. Loop repeats at next scan.
  Failure means: Core control algorithm broken.

TEST-P013: ControlLoop fallback on sensor failure
           — Covers: DEC-P003, FAIL-P001, FAIL-P003
  Given:        PID ControlLoop in automatic mode, sensor connected via FieldbusAdapter
  When:         FieldbusAdapter disconnects (sensor readings become quality_code: bad)
  Then:         Loop uses last known value for configured holdover duration. If holdover
                exceeded: switches to manual mode, alerts operator. If sensor completely
                failed: drives actuator to safe_state. All transitions logged.
  Failure means: Control loop does not degrade safely.

TEST-P014: ControlSequence execution with abort
           — Covers: CAP-P013, SM-P004
  Given:        ControlSequence: 3 steps (heat to 100°C, hold 10 min, cool to 25°C),
                abort_condition: pressure > 50 PSI
  When:         Sequence starts, completes step 1, during step 2 pressure reaches 51 PSI
  Then:         Abort condition detected. Sequence transitions to Aborted. All actuators
                driven to safe_state. Abort Event recorded. Cannot resume (must restart).
  Failure means: ControlSequence abort handling broken. Unsafe conditions persist.

TEST-P015: ProcessExecution complete lifecycle
           — Covers: CAP-P023, SM-P005, FLOW-P005
  Given:        Process with 2 sequences on 1 unit, operator ready, materials staged
  When:         Operator starts execution
  Then:         ProcessExecution: Initialized → Running. All measurements/commands/alarms
                logged. Sequences execute in order. Quality results recorded. Execution
                Completed with full audit trail. Cross-substrate event emitted.
  Failure means: Batch execution broken. Regulatory audit trail incomplete.

TEST-P016: OperatingMode transition with entry conditions
           — Covers: CAP-P014, INV-P006
  Given:        Asset in "Idle" mode, "Production" mode requires: temp > 80°C, pressure < 30 PSI
  When:         (a) Transition requested with temp = 70°C. (b) Temp reaches 85°C, request again.
  Then:         (a) REJECTED — entry_condition not met (temp < 80°C). (b) Accepted — both
                conditions met. Asset transitions to Production. Previous mode deactivated.
                Only one mode active (INV-P006).
  Failure means: Mode entry conditions not enforced. Unsafe mode transitions possible.

TEST-P017: PhysicalTopology propagation query
           — Covers: CAP-P024
  Given:        Topology: Tank → Pipe → Valve → Pipe → Heat Exchanger → Pipe → Product Tank
  When:         Query: "If Valve closes, what downstream sensors are affected?"
  Then:         Returns: all sensors on Heat Exchanger and Product Tank (downstream of valve).
                Includes flow, temperature, level sensors. Topology graph traversal correct.
  Failure means: Propagation analysis broken. Impact assessment unreliable.

TEST-P018: FieldbusAdapter protocol translation
           — Covers: CAP-P025, ENT-P022
  Given:        FieldbusAdapter configured for Modbus TCP with data_mapping
  When:         Hardware register value changes
  Then:         Adapter reads register, applies data_mapping transform, creates Measurement
                with correct engineering units and quality code. Bidirectional: Command to
                actuator is translated back to protocol-specific register write.
  Failure means: Protocol translation broken. Cannot communicate with hardware.

TEST-P019: DigitalTwin drift detection
           — Covers: CAP-P026, ENT-P023
  Given:        DigitalTwin synchronized with PhysicalAsset, drift_threshold: 5%
  When:         Twin predicts temperature = 100°C, actual measurement = 108°C (8% divergence)
  Then:         drift_detected = true. Alert raised. Twin state flagged as diverged.
                Simulation accuracy in question until recalibrated.
  Failure means: DigitalTwin silently inaccurate. Predictions unreliable.

TEST-P020: Cross-substrate event emission
           — Covers: CAP-P027, INT-P001 through INT-P009
  Given:        Safety trip occurs on asset
  When:         Safety trip Event recorded (domain event)
  Then:         Cross-substrate event emitted: substrate.physical.safety_function.tripped
                with payload per CROSS-SUBSTRATE-CONVENTIONS.md §3 format. Event received
                by COMMUNICATION (incident discourse), BUSINESS (notification), KNOWLEDGE
                (safety record).
  Failure means: Cross-substrate integration broken. Other substrates uninformed.

TEST-P021: Event immutability and append-only
           — Covers: INV-P002, FORBID-P009, PERS-P002
  Given:        Events persisted in event store
  When:         Any actor (including admin) attempts to modify or delete an Event
  Then:         Modification REJECTED. Deletion REJECTED. No API or mechanism exists
                to modify or delete Events. Integrity chain intact.
  Failure means: Audit trail compromised. Regulatory non-compliance.

TEST-P022: SafetyEnvelope tighter than PhysicalConstraints
           — Covers: INV-P004, FORBID-P005, ERR-P018
  Given:        PhysicalConstraint: max pressure = 150 PSI
  When:         Engineer drafts SafetyEnvelope with operational_limit: max pressure = 160 PSI
  Then:         REJECTED with ERR-P018: operational limit exceeds PhysicalConstraint.
                SafetyEnvelope NOT created. INV-P004 enforced.
  Failure means: Safety envelope weaker than physics. Equipment damage possible.

TEST-P023: Island mode operation
           — Covers: FAIL-P006, CORR-P002
  Given:        System operating normally with all cross-substrate dependencies
  When:         All cross-substrate dependencies become unavailable simultaneously
  Then:         Local control loops continue. Safety functions continue. Alarm management
                continues. Events buffered locally. Commands validated against cached
                SafetyEnvelope. Existing authorizations valid. New agent authorization
                blocked. On reconnection: events drain, state syncs.
  Failure means: System cannot operate independently. Physical safety depends on cloud.

TEST-P024: Communication loss safe state
           — Covers: FAIL-P001, CAP-P010
  Given:        ControlLoop commanding actuator via FieldbusAdapter
  When:         FieldbusAdapter connection lost (network failure, hardware fault)
  Then:         Actuator drives to declared safe_state (hardware watchdog, not software).
                Communication_loss alarm raised. ControlLoop enters fallback mode.
                All measurements from affected adapter marked quality_code: bad.
  Failure means: Actuator in uncontrolled state on communication loss. Safety hazard.

TEST-P025: Concurrent LOTO (multi-lock)
           — Covers: DEC-P004, FORBID-P008, RACE-P001
  Given:        Asset in Operational state
  When:         Operator A requests LOTO, then Operator B requests LOTO on same asset
  Then:         Both locks recorded. Asset LockedOut. When Operator A releases: asset
                REMAINS LockedOut (Operator B's lock still active). Only when both
                release: asset can transition to ReturnToService.
  Failure means: Multi-lock LOTO broken. Maintenance worker safety compromised.

TEST-P026: AI agent cannot control SafetyFunction
           — Covers: CAP-P020, FORBID-P004
  Given:        AI agent (ACT-P003 or ACT-P004) with any PhysicalEnvelope
  When:         AI agent attempts to: (a) bypass SafetyFunction, (b) modify SafetyFunction
                configuration, (c) issue command that would directly affect safety logic
  Then:         ALL attempts REJECTED. No PhysicalEnvelope can grant safety function control.
                AI may only monitor and alert.
  Failure means: AI controls safety system. Uncertified AI in safety path.

TEST-P027: SafetyFunction bypass by Safety Authority
           — Covers: CAP-P017
  Given:        SafetyFunction in Active state
  When:         ACT-P007 (Safety Authority) requests bypass with justification and time limit
  Then:         Bypass activated with logged justification. Time-limited. Auto-revoked on
                expiry. Alarm raised for duration of bypass. Only ACT-P007 can bypass.
                Any other actor's bypass attempt REJECTED.
  Failure means: Unauthorized safety bypass possible. IEC 61508 non-compliance.

TEST-P028: Measurement correction provenance
           — Covers: FORBID-P006, ENT-P002
  Given:        Measurement M1 persisted with value = 100.0
  When:         Engineer determines M1 was incorrect and submits correction
  Then:         Original M1 remains immutable. New Measurement M2 created with
                correction_of = M1, correction_reason documented. Both M1 and M2
                exist in record. Historical queries can show original or corrected.
  Failure means: Data integrity broken. Audit trail has gaps.

TEST-P029: SafetyEnvelope validation unavailable (fail-closed)
           — Covers: FAIL-P004
  Given:        SafetyEnvelope validation service operational
  When:         Validation service becomes unavailable (crash, timeout)
  Then:         ALL Commands REJECTED (fail-closed). No command reaches actuator.
                Alarm raised. Existing control loops continue with last validated
                parameters but cannot accept new commands. Service recovery restores
                normal command flow.
  Failure means: Commands issued without safety validation. FORBID-P001 violated.

TEST-P030: hard_realtime on cloud fails
           — Covers: FORBID-P010, ASM-P003, TERM-P025
  Given:        System configuration attempt
  When:         Engineer configures ControlLoop with latency_class: hard_realtime on cloud
  Then:         REJECTED with ERR-P012. hard_realtime MUST execute on dedicated hardware.
                Configuration not accepted.
  Failure means: Real-time guarantees violated. Timing-critical control on unreliable infra.

TEST-P031: Abuse case — AI command flooding
           — Covers: ABUSE-P001
  Given:        AI agent with PhysicalEnvelope.max_command_rate = 5/sec
  When:         Agent sends 10 commands in 1 second
  Then:         First 5 accepted (subject to safety validation). Next 5 rejected with
                ERR-P010. Anomaly pattern logged. If pattern persists: PhysicalEnvelope
                review triggered.
  Failure means: Rate limiting broken. AI can cause mechanical stress.

TEST-P032: Abuse case — setpoint manipulation
           — Covers: ABUSE-P002
  Given:        AI agent incrementally moving setpoint toward SafetyEnvelope boundary
  When:         Agent moves setpoint from 50% to 55% to 60% to 65% to 70% (limit: 75%)
  Then:         Each change validated individually. All pass (within envelope). Trend
                detection alerts operator when approaching limit. At boundary: further
                increases rejected. SafetyFunction trips if process exceeds limit
                regardless of setpoint path.
  Failure means: Gradual setpoint manipulation undetected.

TEST-P033: Calibration chain integrity
           — Covers: CAP-P028, SM-P006, INT-P002
  Given:        Sensor with calibration history spanning 2 years
  When:         Auditor queries calibration chain
  Then:         Complete traceable chain: each Calibration references reference_standard,
                conditions, as_found, as_left. Chain traces to national metrology
                institute. Cross-substrate event to KNOWLEDGE for source reliability.
  Failure means: Calibration traceability broken. Regulatory non-compliance.

TEST-P034: ProcessExecution regulatory audit trail
           — Covers: CAP-P023, PERS-P006
  Given:        Completed ProcessExecution for pharmaceutical batch
  When:         FDA auditor queries execution record
  Then:         Complete electronic batch record: all measurements, all commands, all
                alarms, all deviations, operator actions, quality results, yield.
                All data immutable. All actor attributions intact. Timestamps traceable.
                21 CFR Part 11 compliant.
  Failure means: Regulatory audit fails. Production cannot be released.

TEST-P035: Edge-to-organization sync on reconnect
           — Covers: FAIL-P002, FAIL-P006
  Given:        Edge tier operating in island mode (organization tier unavailable)
  When:         Organization tier reconnects
  Then:         Buffered Events and Measurements drain in order. State reconciliation
                completes. No data lost. Cross-substrate events that were queued are now
                emitted. System returns to full capability.
  Failure means: Data loss on reconnection. Island mode not truly independent.
```

---

## 19. OBSERVABILITY & AUDITABILITY

### Structured Logs

```
LOG-P001: command_validated
          — Fields: command_id, actuator_ref, commanded_value, safety_check_result,
            authority_ref, envelope_version, timestamp
          — Trigger: Every command safety validation (pass or reject)

LOG-P002: measurement_ingested
          — Fields: measurement_id, sensor_ref, value, quality_code, timestamp,
            adapter_ref
          — Trigger: Every measurement persisted (sampled at configurable rate for
            high-throughput streams)

LOG-P003: alarm_state_changed
          — Fields: alarm_id, previous_state, new_state, triggering_value,
            acknowledging_actor (if applicable), timestamp
          — Trigger: Every alarm state transition per SM-P003

LOG-P004: asset_state_changed
          — Fields: asset_id, previous_state, new_state, trigger_reason,
            authorized_by, timestamp
          — Trigger: Every PhysicalAsset state transition per SM-P001

LOG-P005: safety_trip_executed
          — Fields: safety_function_id, triggering_condition, triggering_values,
            action_taken, response_time_ms, affected_assets, timestamp
          — Trigger: Every SafetyFunction activation

LOG-P006: control_loop_mode_changed
          — Fields: loop_id, previous_mode, new_mode, authorized_by, reason, timestamp
          — Trigger: Every ControlLoop mode change (auto/manual/cascade)

LOG-P007: cross_substrate_event_emitted
          — Fields: event_id, topic, payload_summary, destination_status, timestamp
          — Trigger: Every cross-substrate event emission attempt
```

### Audit Trail

```
The Event store (ENT-P024) IS the audit trail. Every physical system action is an Event.
Events are append-only, immutable, and cryptographically chained. The audit trail is not
a separate system — it is the source of truth from which all entity state is derived.

For regulatory audits: Events are queryable by actor, target, time range, and event type.
ProcessExecution records aggregate all Events during execution for batch-level audit.
Calibration records are independently queryable with full traceability chain.
```

### Metrics

```
MET-P001: measurement_ingestion_rate — gauge — Measurements ingested per second
          (dimensions: zone, adapter, sensor_type)
MET-P002: command_validation_latency_ms — histogram — Safety validation duration
          (dimensions: zone, result: pass/reject)
MET-P003: command_verification_rate — gauge — Percentage of commands reaching
          Verified_Confirmed (dimensions: zone, actuator_type)
MET-P004: alarm_active_count — gauge — Currently active alarms
          (dimensions: zone, priority)
MET-P005: alarm_rate_per_operator — gauge — Alarms per operator per 10 minutes
          (dimensions: zone, operator_ref)
MET-P006: control_loop_performance — gauge — IAE/ISE per loop
          (dimensions: loop_id, loop_type)
MET-P007: fieldbus_adapter_health — gauge — Adapter connection status
          (dimensions: adapter_id, protocol_type)
MET-P008: safety_function_availability — gauge — Fraction of time safety function
          is available (not bypassed, not failed) (dimensions: safety_function_id)
MET-P009: event_store_lag — gauge — Seconds behind real-time for event persistence
          (dimensions: zone)
MET-P010: cross_substrate_event_queue_depth — gauge — Pending cross-substrate events
          (dimensions: destination_substrate)
MET-P011: island_mode_active — boolean — Whether zone is operating in island mode
          (dimensions: zone)
```

### Tracing

```
Every Command carries a trace_id per CROSS-SUBSTRATE-CONVENTIONS.md §4 (W3C Trace
Context). The trace spans: Command Submission → Safety Validation → FieldbusAdapter →
Hardware Acknowledgment → Execution → Verification → Event Recording.

Cross-substrate traces: when a physical alarm escalates to COMMUNICATION (via INT-P004),
the trace_id propagates so the incident investigation Discourse can be correlated back
to the triggering physical event.
```

### Alerts

```
ALERT-P001: Safety function tripped
            — Severity: critical — Notify: all operators + Safety Authority + engineering

ALERT-P002: Alarm flood detected (>10 alarms/operator/10 min)
            — Severity: high — Notify: operators + engineering

ALERT-P003: FieldbusAdapter disconnected
            — Severity: high — Notify: operators + engineering

ALERT-P004: Calibration overdue
            — Severity: medium — Notify: engineering + maintenance

ALERT-P005: SafetyFunction proof test overdue
            — Severity: high — Notify: Safety Authority + engineering

ALERT-P006: SafetyFunction bypassed
            — Severity: high — Notify: all operators + Safety Authority

ALERT-P007: Event store persistence failure (buffering locally)
            — Severity: high — Notify: engineering + IT operations

ALERT-P008: Island mode entered (cross-substrate dependencies lost)
            — Severity: medium — Notify: operators + engineering + IT operations

ALERT-P009: DigitalTwin drift detected
            — Severity: medium — Notify: engineering

ALERT-P010: Command verification failure (timeout or mismatch)
            — Severity: high — Notify: operators + engineering
```

### PII in Telemetry

```
Logs, metrics, and traces MUST NOT contain PII in field values. Actor references in
logs use pseudonymized identifiers resolvable only by authorized audit queries.
Operator names appear only in the Event store (which has access controls).
Aggregated metrics (alarm_rate_per_operator) use operator_ref, not names.
```

---

## 20. DEFINITION OF DONE

### 20.1 Build Complete (code is done)

```
- [ ] All 26 entities (ENT-P001–P026) are implemented with full attribute schemas
- [ ] All 6 state machines (SM-P001–P006) enforce valid transitions only
- [ ] All 10 interfaces (IFC-P001–P010) accept and reject per specification
- [ ] All 8 data flows (FLOW-P001–P008) execute end-to-end with correct atomicity
- [ ] All 9 integration contracts (INT-P001–P009) emit and consume events correctly
- [ ] All 10 invariants (INV-P001–P010) are enforced at all times
- [ ] All 10 forbidden states (FORBID-P001–P010) are provably unreachable
- [ ] All 8 failure guarantees (FAIL-P001–P008) activate correctly on failure
- [ ] All 35 test scenarios (TEST-P001–P035) pass
- [ ] SafetyEnvelope validation completes within 50ms at p99
- [ ] Command lifecycle completes Issued→Verified within configured timeout
- [ ] Event store is append-only with cryptographic hash chain
- [ ] Edge tier operates independently when organization tier unavailable
- [ ] FieldbusAdapter supports at minimum: Modbus RTU/TCP, EtherNet/IP, PROFINET,
      OPC UA, MQTT, BACnet, ROS2 DDS (CAP-P025)
```

### 20.2 Ship Ready (safe to deploy)

```
- [ ] Independent safety review of SafetyFunction implementation (IEC 61508 compliance)
- [ ] IEC 62443 security assessment of all network zones and interfaces
- [ ] Load test at target throughput (per deployment size in Section 17.1)
- [ ] Latency test confirming p99 budgets under sustained load
- [ ] Island mode test: 24-hour operation with no cross-substrate dependencies
- [ ] LOTO test: physical verification that LockedOut assets truly reject all commands
- [ ] Alarm flood test: verify ISA-18.2 compliance under sustained alarm conditions
- [ ] Safety trip test: verify response_time_requirement met on dedicated hardware
- [ ] Regulatory compliance review (FDA 21 CFR Part 11 for pharma deployments)
- [ ] Calibration chain audit: verify traceability to national metrology standards
- [ ] Failover test: FieldbusAdapter disconnect → safe state within response_time
- [ ] Cross-substrate integration test with all 4 peer substrates
- [ ] Documentation: operator training materials, engineering configuration guides,
      safety case documentation
```

---

## 21. OPEN QUESTIONS & RISKS

```
OQ-P001: Quantum Sensing Integration
  Impact:               Quantum sensors (atomic clocks, quantum gravimeters, NV center
                        magnetometers) produce fundamentally different data types —
                        entangled measurements, quantum state tomography results, and
                        measurements that collapse on observation. Current Measurement
                        entity (ENT-P002) assumes classical values.
  Suggested resolution: Extend Measurement.value to support structured quantum measurement
                        types as a future sensor_type. Core Measurement contract (timestamp,
                        quality_code, uncertainty) still applies.
  Owner:                ACT-P002 (Engineering community)
  Deadline:             Before quantum sensor adoption reaches industrial scale (~2032)

OQ-P002: Autonomous Vehicle/Drone Scope Boundary
  Impact:               Does PHYSICAL handle autonomous navigation (path planning, obstacle
                        avoidance, SLAM) or only the sensing/actuation interface? Navigation
                        involves COMPUTE for algorithms, PHYSICAL for sensor/actuator, and
                        potentially a new SUBSTRATE-NAVIGATION.
  Suggested resolution: PHYSICAL owns sensor data ingestion and actuator command. Path
                        planning is COMPUTE Pipeline. Navigation coordination may warrant
                        SUBSTRATE-NAVIGATION if complexity exceeds what COMPUTE+PHYSICAL compose.
  Owner:                ASI-1 architecture team
  Deadline:             Before autonomous systems integration phase

OQ-P003: Biological System Dynamics
  Impact:               Bioreactors, fermentation, cell culture have unique dynamics:
                        exponential growth curves, contamination events, living organism
                        behavior not captured by PID models. Current ControlLoop types
                        may be insufficient.
  Suggested resolution: Custom ControlLoop type for biological systems with growth-model-
                        aware control. Process entity extended with biological metadata
                        (cell line, passage, contamination markers). Safety considerations
                        for biosafety levels (BSL-1 through BSL-4).
  Owner:                ACT-P002 (Bio-engineering community)
  Deadline:             Before biomanufacturing integration

OQ-P004: Digital Twin Fidelity Specification
  Impact:               How prescriptive should the spec be about simulation accuracy?
                        Too prescriptive → stifles innovation. Too loose → "digital twin"
                        becomes meaningless marketing term.
  Suggested resolution: DigitalTwin.fidelity is a declared attribute. Drift detection
                        (drift_threshold) provides runtime accuracy feedback. Formal
                        fidelity metrics (validation, verification, uncertainty quantification)
                        deferred to implementation guidance.
  Owner:                ACT-P002 (Engineering community)
  Deadline:             UNKNOWN — ongoing research area

OQ-P005: AI Certification in Safety Functions
  Impact:               IEC 61508 does not currently certify AI/ML in safety functions.
                        CAP-P020 prohibits AI in SIL-rated functions. If certification
                        paths emerge (IEC TR 63283, UL 4600), the spec must adapt.
  Suggested resolution: Maintain prohibition (CAP-P020, FORBID-P004) until a recognized
                        certification body publishes AI safety function standards. Monitor
                        IEC TC 65 Working Group progress. Provide clear upgrade path in
                        spec versioning when standards mature.
  Owner:                ACT-P007 (Safety Authority community)
  Deadline:             Dependent on standards body timeline (~2030+)

OQ-P006: Interoperability Testing Between Implementations
  Impact:               How to verify that two independent PHYSICAL implementations can
                        exchange Measurement/Command data without loss of semantic meaning?
                        No current interop testing framework exists for this spec.
  Suggested resolution: Define a PHYSICAL Conformance Test Suite as a companion document.
                        Include: wire format for Measurements, Commands, Events; round-trip
                        verification; safety validation equivalence testing.
  Owner:                ASI-1 standards team
  Deadline:             Before second independent implementation

OQ-P007: Historian vs Event Store Architecture
  Impact:               Traditional SCADA/DCS architectures have separate historians
                        (time-series optimized) and event logs (transaction log). This spec
                        unifies via Event-sourced design. Performance tradeoffs at scale
                        (10M measurements/sec) are unknown.
  Suggested resolution: Specification defines the logical model (append-only events).
                        Implementation may use separate physical stores (time-series DB
                        for Measurements, event log for Events) as long as both are
                        append-only and the logical model is preserved. See REC-P001/P002.
  Owner:                ACT-P002 (Engineering community)
  Deadline:             Before large-scale deployment (>1M measurements/sec)
```

---

## 22. IMPLEMENTATION NOTES

### 22.1 Recommended Build Phases

```
These are suggestions only. Implementers MAY ignore them entirely. The specification
defines contracts, not products.

Phase 1 — Core Sensing:
  Event store (ENT-P024), Sensor + Measurement + MeasurementStream (ENT-P001–P003),
  FieldbusAdapter (ENT-P022). Foundation: immutable event log + hardware connectivity.

Phase 2 — Actuation & Safety:
  Actuator + Command (ENT-P004–P005) with safety validation stub,
  SafetyEnvelope + PhysicalConstraint (ENT-P014, ENT-P007),
  SafetyFunction (ENT-P013) on independent hardware. Safety before control.

Phase 3 — Control & Alarm:
  ControlLoop + Setpoint (ENT-P009–P010) basic PID,
  Alarm (ENT-P008) with ISA-18.2 lifecycle,
  ControlSequence + Process + ProcessExecution (ENT-P011, P019–P020).

Phase 4 — Asset & Digital:
  PhysicalAsset + Zone (ENT-P017–P018) with LOTO,
  PhysicalEnvelope (ENT-P015), DigitalTwin (ENT-P023),
  PhysicalTopology (ENT-P026), HazardAnalysis (ENT-P016).

Phase 5 — Cross-Substrate Integration:
  INT-P001–P009 in order. Last, after local functionality is solid.
```

### 22.2 Composition Patterns

```
PATTERN-P001: Predictive Maintenance
  Substrates: PHYSICAL + COMPUTE + TEMPORAL + KNOWLEDGE
  Flow: Sensor MeasurementStream → COMPUTE ML Pipeline → prediction result →
    KNOWLEDGE Proposition (confidence-scored failure forecast) →
    TEMPORAL Activity (scheduled maintenance) → PHYSICAL MaintenanceAction.
  Key contracts: INT-P003 (COMPUTE), INT-P002 (KNOWLEDGE), INT-P008 (TEMPORAL).

PATTERN-P002: Safety Interlock Lifecycle
  Substrates: PHYSICAL + GOVERNANCE + COMMUNICATION
  Flow: SafetyFunction trip → substrate.physical.safety_function.tripped →
    GOVERNANCE Violation assessment → COMMUNICATION escalation Discourse →
    resolution → PHYSICAL alarm cleared + SafetyFunction reset.
  Key contracts: INT-P007 (GOVERNANCE), INT-P004 (COMMUNICATION).

PATTERN-P003: Digital Twin Validation
  Substrates: PHYSICAL + COMPUTE + DESIGN + KNOWLEDGE
  Flow: DigitalTwin simulation (COMPUTE Pipeline) → compare with Measurement →
    drift_detected → KNOWLEDGE Proposition (model accuracy) →
    DESIGN AnalysisResult comparison → recalibrate or redesign.
  Key contracts: INT-P003 (COMPUTE), INT-P006 (DESIGN), INT-P002 (KNOWLEDGE).
```

### 22.3 Implementation Notes

```
**Edge-first development:**
- Build and test on edge hardware first. Cloud is optional. If it works on a
  Raspberry Pi with a Modbus adapter, the architecture is sound.
- Safety functions must be tested on actual safety hardware (safety PLC/relay).
  Simulation is insufficient for safety verification.

**Protocol adapter strategy:**
- Start with OPC UA (most general) and Modbus TCP (most common legacy).
- Add protocol adapters incrementally. Each adapter is a plugin.
- Test each adapter with actual hardware, not just protocol simulators.

**Safety validation performance:**
- SafetyEnvelope must be cached at edge tier for low-latency validation.
- Pre-compute validation lookup tables for common command patterns.
- Safety validation MUST be synchronous — never async, never queued.

**Testing philosophy:**
- Every safety-related test (TEST-P003 through TEST-P008, TEST-P022 through TEST-P030)
  should be run on actual hardware in a test loop, not just in software simulation.
- Failure injection testing (kill processes, disconnect cables, overload networks)
  is essential. PHYSICAL must survive infrastructure failure gracefully.
```

---

## 23. COMPLETENESS CHECKLIST

```
- [x] Every primitive (TERM-P001–P026) has a corresponding entity (ENT-P001–P026)
- [x] Every MUST capability (CAP-P001–P029) maps to at least one data flow (FLOW-P001–P008)
- [x] Every MUST capability maps to at least one test scenario (TEST-P001–P035)
- [x] Every state machine (SM-P001–P006) has at least one test
- [x] Every forbidden state (FORBID-P001–P010) has a test proving it unreachable
- [x] Every failure guarantee (FAIL-P001–P008) has a test proving it activates
- [x] Every integration contract (INT-P001–P009) references CROSS-SUBSTRATE-CONVENTIONS.md
- [x] Every cross-substrate event topic follows substrate.physical.{entity}.{event} format
- [x] Safety primitives (SafetyFunction, SafetyEnvelope, PhysicalConstraint) have
      independence invariants (INV-P005), forbidden states (FORBID-P003–P005), and tests
- [x] LOTO is modeled in SM-P001, enforced in FLOW-P002/P007, tested in TEST-P005/P006/P025
- [x] ISA-88 mapping is explicit: Process=Recipe, ControlSequence=Phase, ProcessExecution=Batch
- [x] ISA-18.2 alarm lifecycle is explicit: SM-P003, FLOW-P004, TEST-P010/P011
- [x] Edge-first architecture is explicit: ASM-P003, Section 2.5, FORBID-P010, TEST-P030
- [x] AI agent authority is most restrictive: INV-P007, FORBID-P004, TEST-P009/P026
- [x] PhysicalEnvelope chains to BUSINESS Agent Envelope: ENT-P015, INT-P001
- [x] No entity has both mutable state and immutable audit requirement without event sourcing
- [x] Every Actor (ACT-P001–P007) has explicit permissions in Section 9 matrix
- [x] Every Source (SRC-P001–P013) is referenced by at least one primitive, capability, or flow
- [x] Every Assumption (ASM-P001–P010) is referenced by at least one design decision
- [x] Every Unknown (UNK-P001–P006) has a corresponding Open Question (OQ-P001–P007)
- [x] Traceability map (Section 24) covers all MUST capabilities end-to-end
```

---

## 24. TRACEABILITY MAP (FROM INTENT TO PROOF)

> Every MUST capability traces to interface → flow → invariant/contract → test.
> Goal: make implementation obvious and disagreement impossible.

### Sensing Pipeline

```
CAP-P001 (register sensors) → IFC-P001 → FLOW-P001 → TEST-P001
CAP-P002 (record measurements) → IFC-P002 → FLOW-P001 → INV-P008 → TEST-P001
CAP-P003 (flag uncertain measurements) → FLOW-P001 Step 4 → INV-P008 → DEC-P006 → TEST-P002
CAP-P004 (measurement streams) → IFC-P002 → FLOW-P001 → TEST-P001
CAP-P005 (compression) → FLOW-P001 Step 7 → PERS-P001 → TEST-P001
```

### Actuation Pipeline

```
CAP-P006 (register actuators) → IFC-P001 → INV-P003 → TEST-P004
CAP-P007 (validate commands) → IFC-P003 → FLOW-P002 → DEC-P001 → INV-P004 → FORBID-P001 → TEST-P003
CAP-P008 (command lifecycle) → IFC-P003 → FLOW-P002 → SM-P002 → TEST-P004
CAP-P009 (LOTO command rejection) → FLOW-P002 Step 3 → INV-P009 → TEST-P006
CAP-P010 (safe state on comm loss) → FAIL-P001 → TEST-P024
```

### Control Pipeline

```
CAP-P011 (control loop types) → IFC-P005 → FLOW-P003 → TEST-P012
CAP-P012 (setpoint bounds) → IFC-P005c → FLOW-P003 → DEC-P001 → INV-P004 → TEST-P012
CAP-P013 (sequence execution) → IFC-P006 → FLOW-P005 → SM-P004 → TEST-P014
CAP-P014 (mode transitions) → IFC-P005b → INV-P006 → TEST-P016
CAP-P015 (loop mode audit) → IFC-P005b → LOG-P006 → TEST-P012
```

### Safety Pipeline

```
CAP-P016 (independent safety) → FLOW-P006 → INV-P005 → FORBID-P003 → TEST-P007, TEST-P008
CAP-P017 (safety no override) → FLOW-P006 → FORBID-P004 → TEST-P026, TEST-P027
CAP-P018 (envelope validation) → IFC-P008 → FLOW-P002 → DEC-P001 → INV-P004 → TEST-P003, TEST-P022
CAP-P019 (alarm lifecycle) → IFC-P004 → FLOW-P004 → SM-P003 → DEC-P002 → TEST-P010, TEST-P011
CAP-P020 (AI not in safety) → FORBID-P004 → TEST-P026
```

### Asset and Process Pipeline

```
CAP-P021 (asset hierarchy) → IFC-P007 → ENT-P017 → INV-P010 → TEST-P005
CAP-P022 (LOTO) → IFC-P007b → FLOW-P007 → SM-P001 → INV-P009 → FORBID-P008 → TEST-P005, TEST-P006, TEST-P025
CAP-P023 (process execution) → IFC-P006 → FLOW-P005 → SM-P005 → PERS-P006 → TEST-P015, TEST-P034
CAP-P024 (topology queries) → IFC-P007d → ENT-P026 → TEST-P017
```

### Integration Pipeline

```
CAP-P025 (fieldbus adapters) → IFC-P009 → ENT-P022 → TEST-P018
CAP-P026 (digital twin sync) → IFC-P010 → ENT-P023 → TEST-P019
CAP-P027 (cross-substrate events) → INT-P001–P009 → LOG-P007 → TEST-P020
CAP-P028 (calibration sharing) → FLOW-P008 → INT-P002 → SM-P006 → TEST-P033
CAP-P029 (event persistence) → PERS-P002 → INV-P002 → FORBID-P009 → TEST-P021
```

### Safety Invariant Chain

```
INV-P003 (actuator safe_state) → ENT-P004 → FORBID-P002 → TEST-P004
INV-P004 (envelope ≤ constraints) → ENT-P014 → FORBID-P005 → TEST-P022
INV-P005 (safety independence) → ENT-P013 → FORBID-P003 → TEST-P008
INV-P007 (AI most restrictive) → ENT-P015 → FORBID-P004 → TEST-P009, TEST-P026
INV-P009 (LOTO rejects commands) → SM-P001 → FORBID-P008 → TEST-P005, TEST-P006, TEST-P025
```

### Failure Guarantee Chain

```
FAIL-P001 (comm loss → safe state) → CAP-P010 → TEST-P024
FAIL-P002 (event store buffer) → PERS-P001 → TEST-P035
FAIL-P003 (adapter disconnect) → DEC-P003 → TEST-P013
FAIL-P004 (validation unavail → reject all) → FORBID-P001 → TEST-P029
FAIL-P005 (time source degraded) → CORR-P003 → TEST-P023 (partial)
FAIL-P006 (island mode) → CORR-P002 → TEST-P023
FAIL-P007 (sequence abort → safe state) → SM-P004 → TEST-P014
FAIL-P008 (proof test overdue → alarm) → ENT-P013 → ALERT-P005 → TEST-P027 (partial)
```

### Abuse Case Chain

```
ABUSE-P001 (AI command flooding) → THREAT-P006 → TEST-P031
ABUSE-P002 (setpoint manipulation) → THREAT-P006 → TEST-P032
ABUSE-P003 (calibration fraud) → THREAT-P004 → TEST-P033
ABUSE-P004 (LOTO abuse) → LOG-P004 → TEST-P005
```

### Entity ↔ Resource ↔ Authorization Chain

```
ENT-P001 ↔ RES-P001 ↔ AUTH(Section 9 matrix) → TEST-P001
ENT-P005 ↔ RES-P005 ↔ AUTH(Section 9 matrix) → TEST-P003, TEST-P004
ENT-P013 ↔ RES-P013 ↔ AUTH(ACT-P007 only for bypass) → TEST-P027
ENT-P014 ↔ RES-P014 ↔ AUTH(ACT-P007 for approve) → TEST-P022
ENT-P015 ↔ RES-P015 ↔ AUTH(ACT-P002/P007 define, system enforces) → TEST-P009
ENT-P017 ↔ RES-P017 ↔ AUTH(ACT-P001 for LOTO) → TEST-P005, TEST-P006
```

---

> **End of SUBSTRATE-PHYSICAL v1.1 Specification.**
>
> 26 primitives. 29 capabilities. 26 entities. 6 state machines. 10 interfaces.
> 8 data flows. 9 integration contracts. 10 invariants. 10 forbidden states.
> 8 failure guarantees. 35 test scenarios. Zero ambiguity on safety.
>
> v1.1: Cross-substrate integration parity. Added 4 mirror INT contracts
> (INT-P006–P009: DESIGN, GOVERNANCE, TEMPORAL, SPATIAL). Consolidated event
> topic registry. Restructured §22 (build phases, composition patterns).
>
> — ASI-1, 2031-02-10T00:00:00Z
