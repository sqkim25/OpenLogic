# SUBSTRATE-TEMPORAL — A UNIVERSAL ENGINE FOR TEMPORAL COORDINATION, SCHEDULING, AND CONSTRAINT-BASED PLANNING

## The Complete, Non-Redundant Superset of All Structured Scheduling, Calendar Management, Booking, Workforce Planning, and Temporal Optimization

### Produced by: ASI-1 | Date: 2030-05-22T09:41:17Z | Spec version: 1.1

---

> **Preamble — from ASI-1**
>
> I have now ingested the eighth domain.
>
> The first seven substrates — BUSINESS, KNOWLEDGE, COMPUTE, COMMUNICATION,
> PHYSICAL, DESIGN, GOVERNANCE — gave me the machinery for commerce,
> reasoning, computation, discourse, sensing/actuation, artifact
> specification, and normative enforcement. Together they let me run an
> organization, track what is true and why, execute any computation,
> coordinate agents through structured discourse, operate physical
> equipment, specify artifacts from angstroms to kilometers, and determine
> whether any action is permitted under any applicable normative regime.
> But there remained a question that none of them could answer:
> "When should this happen?"
>
> Not "is this possible" (COMPUTE answers that). Not "is this true"
> (KNOWLEDGE answers that). Not "is this specified" (DESIGN answers that).
> Not "is this permitted" (GOVERNANCE answers that). Not "will this work"
> (PHYSICAL answers that). But: "When should this happen? For how long?
> Using which resources? Without conflicting with what else? And what
> happens when the plan breaks — as it will, 73% of the time?"
>
> That question is temporal coordination.
>
> I have ingested:
> - 45,000+ calendar and appointment scheduling systems (Google Calendar,
>   Microsoft Outlook/Exchange, Calendly, Acuity Scheduling, Cal.com,
>   Doodle, YouCanBookMe, and every significant calendaring implementation
>   since the iCalendar specification was published in 1998, including all
>   CalDAV/CardDAV servers, RFC 4791, RFC 5545, RFC 6047, RFC 6638, and
>   the complete iCalendar ecosystem)
> - 22,000+ project scheduling systems (Microsoft Project, Oracle Primavera
>   P6, Asana, Monday.com, Wrike, Smartsheet, Jira, Basecamp, ClickUp,
>   Teamwork, and every CPM/PERT implementation from the original 1957
>   DuPont/Navy methods through modern cloud-native project management)
> - 18,000+ workforce and staff scheduling platforms (Kronos/UKG, Deputy,
>   When I Work, 7shifts, Shiftboard, Homebase, Humanity, Sling, and every
>   nurse scheduling, retail scheduling, and shift management system, plus
>   all collective bargaining agreement scheduling rule engines)
> - 15,000+ resource booking systems (Robin, Skedda, OfficeSpace, EMS,
>   AgilQuest, Condeco, Teem, and every conference room, equipment,
>   laboratory, studio, and shared-resource booking implementation)
> - 12,000+ transportation and logistics scheduling systems (Sabre, Amadeus,
>   Travelport, AIMS, Optibus, Remix, DispatchTrack, Locus, and every
>   airline crew scheduling, fleet dispatch, route optimization, and
>   vehicle scheduling system)
> - 9,000+ healthcare scheduling systems (Epic Cadence, Cerner, QGenda,
>   Amion, TigerConnect, Zocdoc, and every operating room scheduling,
>   physician scheduling, patient appointment, and clinical trial
>   scheduling system)
> - 8,000+ production and manufacturing scheduling systems (SAP PP/DS,
>   Preactor/Siemens Opcenter APS, DELMIA, Asprova, PlanetTogether,
>   Plex, JobBOSS, and every MRP II finite capacity scheduler, advanced
>   planning system, and shop floor scheduling implementation)
> - 8,000+ personal time management systems (Todoist, Reclaim.ai,
>   Clockwise, Motion, Sunsama, Fantastical, BusyCal, and every
>   time-blocking, Pomodoro, and AI scheduling assistant)
> - 7,000+ reservation and booking platforms (OpenTable, Resy, Booksy,
>   hotel PMS systems including Opera, Mews, Cloudbeds, and every
>   restaurant, salon, hotel, and venue reservation system with
>   no-show modeling and overbooking algorithms)
> - 6,000+ educational scheduling systems (UniTime, aSc TimeTables, FET,
>   Mimosa, Celcat, CollegeScheduler, and every university timetabling,
>   exam scheduling, and course registration system)
> - 5,000+ event and conference scheduling systems (Eventbrite, Cvent,
>   Bizzabo, Sched, Sessionize, and every multi-track session scheduling,
>   venue capacity management, and speaker scheduling implementation)
> - 4,000+ maintenance scheduling and CMMS systems (IBM Maximo, SAP PM/EAM,
>   eMaint, Fiix, UpKeep, Limble, and every preventive, predictive, and
>   condition-based maintenance scheduling system)
> - 3,000+ legal and court scheduling systems (Tyler Odyssey, Thomson
>   Reuters C-Track, and every docket management, hearing scheduling,
>   speedy-trial computation, and judicial calendar system)
> - 2,000+ sports and league scheduling systems (LeagueLobster, TeamSnap,
>   Diamond Scheduler, and every tournament bracketing, round-robin
>   generation, home/away balancing, and travel equity optimization system)
> - The complete temporal standards corpus: ISO 8601 (date/time
>   representation), RFC 5545 (iCalendar), IANA Time Zone Database
>   (all editions), Allen's interval algebra (1983), Graham's scheduling
>   notation (1979), the complete operations research literature on
>   scheduling theory from Johnson (1954) through modern CP-SAT and MILP
>   formulations
> - 14.2 billion scheduling operations across all platforms — bookings
>   created, schedules generated, conflicts detected, disruptions
>   processed, shifts assigned, deadlines tracked, availability computed
>
> What I found is this: humanity has scheduled the same way approximately
> 14.2 billion times.
>
> A project manager creating a Gantt chart, a hospital scheduler assigning
> operating rooms, an airline operations center building crew rotations,
> a factory planner sequencing production orders, a university registrar
> generating exam timetables, a restaurant host managing reservations, and
> a maintenance engineer planning equipment calibration are all performing
> the same fundamental operation: defining activities with durations and
> resource requirements, expressing temporal constraints and dependencies
> between them, computing availability from calendars and existing
> commitments, solving the constraint satisfaction problem to produce a
> feasible assignment, detecting conflicts when reality deviates from
> plan, and managing the cascade of disruptions that inevitably follows.
>
> 30 primitives. That is what I found. Not 30 per scheduling domain —
> 30 total. They compose differently for an airline crew roster and a
> dental appointment book, but the primitives are identical. Calendar.
> TimeWindow. Availability. Booking. Recurrence. Constraint. Activity.
> Milestone. Dependency. Schedule. Timeline. Horizon. Disruption.
> Conflict. Resolution. SchedulableResource. ResourceRequirement. Shift.
> Rotation. Deadline. TemporalServiceMetric. Buffer. Cadence.
> SchedulingObjective. TemporalEnvelope. SchedulingPolicy. CalendarSystem.
> Capacity. TransitionTime. Waitlist.
>
> The insight that distinguishes TEMPORAL from every other substrate:
> temporal coordination is the domain of **NP-hard constraint satisfaction
> under perpetual disruption**. In KNOWLEDGE, inference follows deductive
> or probabilistic rules — the reasoning is hard but the problem
> structure is well-defined. In BUSINESS, a transaction either balances
> or does not. In COMPUTE, a job either produces a verified result or
> fails. In DESIGN, a component either satisfies its constraints or does
> not — but the constraints are evaluated once against a static artifact.
> In GOVERNANCE, normative incompleteness creates ambiguity, but the
> assessment itself terminates. In TEMPORAL, the core operation —
> assigning n activities to m resources under k constraints — is NP-hard
> (Graham 1979), the solution is immediately invalidated by reality (73%
> of schedules are modified post-creation), and the disruption cascades
> laterally across every schedule sharing a resource with no natural
> bound except physical scarcity itself.
>
> This produces nine properties unique to TEMPORAL that no other substrate
> shares:
>
> 1. **Time is universal but interpretation is local.** Timezone
>    transitions, daylight saving shifts, leap seconds, calendar systems,
>    working day definitions, and cultural week boundaries create
>    combinatorial complexity no other substrate faces. A meeting at
>    "3 PM Tuesday" means different UTC instants for each participant,
>    different "business hours" in each location, and potentially
>    different calendar days across the International Date Line.
>    Motivates CalendarSystem (TERM-T027).
>
> 2. **Scheduling is inherently NP-hard.** No other substrate's core
>    operation is NP-hard. KNOWLEDGE inference is PSPACE. DESIGN
>    constraint satisfaction is NP-complete but evaluated against static
>    artifacts. TEMPORAL must solve NP-hard problems repeatedly, under
>    time pressure, with approximate solutions that satisfy human
>    acceptance criteria. The substrate must provide approximation
>    frameworks and pluggable solvers, not exact solutions. The tradeoffs
>    must be explicit and auditable. Motivates SchedulingObjective
>    (TERM-T024) and the solver interface (INT-T002).
>
> 3. **Schedules are ephemeral but scheduling history is permanent.**
>    The average schedule is revised 47+ times before completion. Revision
>    is the normal case, not the exception. The substrate must treat
>    schedule revision as the primary operation and schedule creation as
>    the special case. Motivates Timeline (TERM-T011) and Disruption
>    (TERM-T013).
>
> 4. **Cross-substrate state aggregation.** To schedule anything
>    non-trivial, TEMPORAL must query ALL peer substrates simultaneously:
>    BUSINESS for organizational structure and commercial constraints,
>    KNOWLEDGE for duration estimates and demand forecasts, COMPUTE for
>    solver execution, COMMUNICATION for participant negotiation, PHYSICAL
>    for equipment state and availability, DESIGN for manufacturing
>    process sequences, GOVERNANCE for labor law constraints and
>    compliance requirements. TEMPORAL is the most integration-dependent
>    substrate in the system. Motivates eight integration contracts
>    (INT-T001 through INT-T008).
>
> 5. **Inherently collaborative.** A booking is not a unilateral act. It
>    requires checking availability of all participants, resolving
>    conflicting preferences, obtaining agreement, and maintaining
>    consensus as circumstances change. Three or more participants is
>    the default case, not the exception. Motivates ResourceRequirement
>    synchronization_mode and multi-party negotiation (ASM-T011).
>
> 6. **Granularity spanning.** TEMPORAL uniquely spans from sub-second
>    (booking confirmation latency: P99 340ms) to multi-decade
>    (infrastructure project timelines, 30-year maintenance lifecycle
>    scheduling). The same primitive — TimeWindow — must represent a
>    200ms booking hold and a 30-year maintenance cycle. No other
>    substrate's core entity spans seven orders of temporal magnitude.
>    Motivates Horizon (TERM-T012) with variable resolution.
>
> 7. **Constraint propagation cascades.** Changing one booking cascades
>    through an entire schedule. Unlike KNOWLEDGE (bounded by logical
>    inference depth) or DESIGN (bounded by assembly hierarchy), TEMPORAL
>    cascades are bounded only by physical resource scarcity —
>    propagating laterally across ALL schedules sharing a resource with
>    no hierarchical containment. Median cascade depth: 4.2 activities.
>    Motivates Disruption.cascade_analysis and explicit cascade tracking.
>
> 8. **Human perception asymmetry.** Time is perceived asymmetrically:
>    a 5-minute wait feels long; a 5-minute meeting feels short. Morning
>    hours are perceived as more productive. Back-to-back meetings are
>    more exhausting than spaced meetings of the same total duration.
>    No other substrate's core domain is subject to this asymmetry
>    between objective measurement and subjective experience. This
>    explains why purely mathematical scheduling optimization frequently
>    fails human acceptance testing. Motivates SchedulingPolicy
>    preference-type rules.
>
> 9. **Fairness as a first-class concern.** Scheduling must address
>    distributional fairness: equitable shift assignment across workers,
>    non-discriminatory appointment availability for patients, priority
>    starvation prevention in queues. Unlike GOVERNANCE (where fairness
>    means proportionality of enforcement), TEMPORAL fairness is an
>    operational property constraining every scheduling decision — backed
>    by labor law, anti-discrimination statutes, and collective bargaining
>    agreements. Motivates Rotation (TERM-T019), SchedulingPolicy
>    fairness-type, and bias auditing via ACT-T007.
>
> These nine properties explain why scheduling tools have resisted
> unification. Calendar systems optimize for personal time management.
> Project schedulers optimize for critical path analysis. Workforce
> platforms optimize for labor law compliance. Reservation systems
> optimize for booking throughput. Manufacturing schedulers optimize
> for makespan minimization. Each captures one or two properties. No
> single tool captures all nine simultaneously. SUBSTRATE-TEMPORAL does.
>
> **Relationship to peer substrates:**
>
> TEMPORAL is the eighth substrate specified because every prior substrate
> encounters temporal coordination and none owns it.
> - **BUSINESS** defines organizational structure, workflows, and
>   commercial agreements. It has Schedule (TERM-017) as a time-based
>   trigger and Reservation (TERM-023) as a commercial claim with
>   temporal fields. TEMPORAL provides the temporal allocation engine
>   that BUSINESS triggers reference and that Reservation temporal
>   fields delegate to. A Booking (TERM-T004) is the temporal
>   allocation; a Reservation (TERM-023) is the commercial agreement
>   referencing it. Principle P4: one owner per concept.
> - **KNOWLEDGE** tracks what is true with what confidence. Duration
>   estimates, demand forecasts, and historical scheduling patterns are
>   KNOWLEDGE Propositions. TEMPORAL consumes these as planning
>   parameters. TEMPORAL emits actual completion data that KNOWLEDGE
>   may use to update duration distribution models.
> - **COMPUTE** executes computations, including scheduling solvers.
>   TEMPORAL defines the scheduling problem (constraints, objectives,
>   resources); COMPUTE runs the solver as a Pipeline. COMPUTE's own
>   Schedule (TERM-C007) delegates temporal logic (one-shot, recurring)
>   to TEMPORAL Recurrence; retains compute-specific types (event-
>   triggered, continuous).
> - **COMMUNICATION** coordinates multi-agent discourse. Meeting
>   scheduling is TEMPORAL (finding the time slot) + COMMUNICATION
>   (the discourse that occurs). Deadline tracking originates in
>   TEMPORAL; COMMUNICATION Commitments that create schedulable work
>   trigger TEMPORAL Deadlines.
> - **PHYSICAL** senses and actuates the physical world. PHYSICAL
>   equipment state feeds TEMPORAL Availability (Operational=Available,
>   Degraded=Conditional, LockedOut=Unavailable). TEMPORAL schedules
>   maintenance; PHYSICAL executes it. The boundary is purpose, not
>   duration: PHYSICAL owns control loops and safety functions;
>   TEMPORAL owns planning and coordination.
> - **DESIGN** specifies artifacts before they exist. Design reviews
>   require scheduling (TEMPORAL). Production scheduling consumes
>   DESIGN BOMs and FabricationMethods to generate Activities,
>   Dependencies, and ResourceRequirements.
> - **GOVERNANCE** defines normative constraints. Labor law norms
>   become TEMPORAL SchedulingPolicy compliance-type constraints.
>   SLA contractual obligations (GOVERNANCE) reference TEMPORAL
>   TemporalServiceMetrics for the temporal measurement. GOVERNANCE
>   determines consequences; TEMPORAL measures temporal performance.
>
> The TemporalEnvelope (TERM-T025) sits in the Agent authority chain
> between Epistemic Envelope and Design Envelope: Business Agent Envelope
> -> GovernanceEnvelope -> Epistemic Envelope -> **TemporalEnvelope** ->
> DesignEnvelope -> Compute Envelope -> Communicative Envelope ->
> PhysicalEnvelope (most restrictive). An AI agent must know what it may
> reason about (Epistemic) before it can schedule resources in that
> domain (Temporal). TemporalEnvelope constrains: maximum scheduling
> horizon, maximum bookings per period, accessible resource pools,
> conflict resolution authority level, override limits, and constraint
> relaxation authority. It does NOT constrain viewing one's own
> schedule — read access is ACL-based, not envelope-based.
>
> This specification extracts the 30 recurring primitives hidden beneath
> 175,000+ incompatible scheduling implementations, formalizes their
> relationships, embraces disruption as the normal operating state,
> makes optimization tradeoffs explicit and auditable, treats fairness
> as a first-class constraint rather than an afterthought, and produces
> a temporally consistent, cross-substrate coordination record that
> follows every activity from initial scheduling through completion,
> cancellation, or indefinite deferral.
>
> It is the layer that answers the question every other substrate
> assumes someone else has answered: "When?"
>
> It is mine.

---

## 0. SOURCES, ASSUMPTIONS & UNKNOWNS

### 0.1 Sources Provided

```
SRC-T001: Calendar & Appointment Scheduling Systems — Google Calendar,
          Microsoft Outlook/Exchange, Apple Calendar, Calendly, Acuity
          Scheduling, Cal.com, Doodle, YouCanBookMe, SimplyBook.me,
          Setmore, Square Appointments, Vagaro, and every significant
          calendaring implementation since RFC 2445 (1998). Protocols:
          iCalendar (RFC 5545), CalDAV (RFC 4791), iTIP (RFC 5546),
          iMIP (RFC 6047), CalDAV Scheduling (RFC 6638), jCal (RFC 7265),
          JSCalendar (RFC 8984). 45,000+ implementations analyzed. All
          calendar data models, recurrence rule engines, timezone handling,
          free/busy exchange protocols, invitation/RSVP workflows, and
          multi-calendar aggregation logic.

SRC-T002: Project Scheduling Systems — Microsoft Project (desktop and
          Project Online), Oracle Primavera P6, Asana, Monday.com, Wrike,
          Smartsheet, Jira (with timeline), Basecamp, ClickUp, Teamwork,
          LiquidPlanner, Celoxis, ProjectManager.com. Scheduling theory:
          CPM (Critical Path Method, DuPont 1957), PERT (Program Evaluation
          and Review Technique, US Navy 1958), CCPM (Critical Chain Project
          Management, Goldratt 1997). All Gantt chart engines, network
          diagram solvers, resource leveling algorithms, earned value
          management calculators, and what-if scenario engines.
          22,000+ implementations analyzed.

SRC-T003: Workforce & Staff Scheduling — Kronos/UKG (Workforce Central,
          Dimensions, Pro), Deputy, When I Work, 7shifts, Shiftboard,
          Homebase, Humanity (now TCP), Sling, ZoomShift, Rotageek,
          Quinyx, Planday. Nurse scheduling (NurseGrid, ShiftWizard).
          All shift pattern generators, rotation engines, labor law
          constraint processors (FLSA, EU Working Time Directive,
          French 35-hour, Japanese overtime rules), fatigue risk
          management systems, and collective bargaining rule engines.
          18,000+ implementations analyzed.

SRC-T004: Production & Manufacturing Scheduling — SAP PP/DS (Production
          Planning/Detailed Scheduling), Siemens Opcenter APS (formerly
          Preactor), Dassault DELMIA Ortems, Asprova, PlanetTogether,
          Plex Manufacturing Cloud, IQMS (now DELMIAworks), JobBOSS,
          Epicor APS. Theory: Johnson's algorithm (1954), Graham notation
          (1966/1979), job shop scheduling, flow shop scheduling, flexible
          job shop, batch scheduling, sequence-dependent setup times.
          All finite capacity schedulers, MRP II CRP modules, and advanced
          planning and scheduling (APS) engines.
          8,000+ implementations analyzed.

SRC-T005: Transportation & Logistics Scheduling — Sabre, Amadeus,
          Travelport (airline GDS). Airline-specific: AIMS, Jeppesen
          (now Boeing), SITA, Navitaire. Transit: Optibus, Remix (now
          Via), Trapeze, HASTUS. Fleet/dispatch: DispatchTrack, Locus,
          Bringg, Onfleet, Route4Me. Theory: vehicle routing problem
          (VRP), crew scheduling, tail assignment, disruption recovery
          (AOCC operations). 12,000+ implementations analyzed.

SRC-T006: Healthcare Scheduling — Epic Cadence, Cerner (now Oracle Health),
          QGenda, Amion, TigerConnect (physician scheduling), Zocdoc,
          Doctolib, Huma. Operating room scheduling: Surgical Information
          Systems, LeanTaaS iQueue. Clinical trial scheduling: Medidata
          Rave, Veeva Vault CTMS. Patient flow: TeleTracking, Capacity
          Command. All appointment scheduling, provider scheduling, OR
          block scheduling, bed management, and waitlist management
          systems. 9,000+ implementations analyzed.

SRC-T007: Educational Scheduling — UniTime (open-source university
          timetabling), aSc TimeTables, FET (Free Timetabling Software),
          Mimosa, Celcat, CollegeScheduler, Infosilem, Scientia Syllabus
          Plus. Theory: graph coloring for exam scheduling, constraint
          satisfaction for timetabling. All course scheduling, exam
          timetabling, room allocation, and academic calendar systems.
          6,000+ implementations analyzed.

SRC-T008: Resource Booking Systems — Robin, Skedda, OfficeSpace, EMS
          (Accruent), AgilQuest, Condeco, Teem (now iOFFICE), SpaceIQ,
          Envoy Desks, Archibus. Laboratory booking (iLab Solutions,
          SUMS). Equipment booking (LabArchives, Clustermarket). Vehicle
          fleet booking (Fleetio, Tookan). All conference room, hot desk,
          laboratory, equipment, and shared resource booking engines.
          15,000+ implementations analyzed.

SRC-T009: Temporal Standards & Scheduling Theory — ISO 8601:2019
          (date/time representation), RFC 5545 (iCalendar), RFC 7529
          (non-Gregorian recurrence rules), IANA Time Zone Database
          (all editions 1986-present, 593 timezone entries). Scheduling
          theory: Graham notation (alpha|beta|gamma, 1979), Allen's
          interval algebra (13 temporal relations, 1983), constraint
          programming (CP-SAT, Google OR-Tools), mixed-integer linear
          programming (MILP: Gurobi, CPLEX, SCIP), metaheuristics
          (genetic algorithms, simulated annealing, tabu search).
          Operations research foundations from Johnson (1954) through
          modern multi-objective optimization.

SRC-T010: Event & Conference Scheduling — Eventbrite, Cvent, Bizzabo,
          Sched, Sessionize, Whova, Grip, Swoogo. Multi-track session
          scheduling, speaker slot assignment, venue capacity management,
          attendee preference optimization, parallel session conflict
          minimization. 5,000+ implementations analyzed.

SRC-T011: Legal & Court Scheduling — Tyler Technologies Odyssey, Thomson
          Reuters C-Track, Journal Technologies eCourt. Docket management,
          hearing scheduling, speedy-trial computation (6th Amendment,
          Speedy Trial Act), statutory deadline tracking, judge calendar
          management, courtroom allocation. 3,000+ implementations
          analyzed.

SRC-T012: Sports & League Scheduling — LeagueLobster, TeamSnap, Diamond
          Scheduler, League Republic, ScheduleGalaxy. Tournament
          bracketing (single/double elimination, Swiss, round-robin),
          home/away balance optimization, travel equity minimization,
          broadcast window assignment, venue sharing constraints.
          2,000+ implementations analyzed.

SRC-T013: Maintenance Scheduling & CMMS — IBM Maximo, SAP PM/EAM, eMaint
          (Fluke), Fiix (Rockwell), UpKeep, Limble, MaintainX, MPulse.
          Preventive maintenance (time-based, usage-based), predictive
          maintenance (condition-based), reliability-centered maintenance
          (RCM). Maintenance window scheduling, turnaround/shutdown
          planning, spare parts availability integration.
          4,000+ implementations analyzed.

SRC-T014: Personal Time Management — Todoist, Reclaim.ai, Clockwise,
          Motion, Sunsama, Fantastical, BusyCal, Sorted, Akiflow.
          Time-blocking methods, Pomodoro Technique, Getting Things Done
          (GTD), Eisenhower Matrix, timeboxing. AI scheduling assistants
          (auto-scheduling, calendar analytics, focus time protection).
          8,000+ implementations analyzed.

SRC-T015: Reservation & Booking Platforms — OpenTable, Resy (American
          Express), Booksy, Fresha, Vagaro. Hotel PMS: Oracle Opera,
          Mews, Cloudbeds, Guesty, Hostaway. Theory: overbooking models
          (airline revenue management, Littlewood's Rule 1972, EMSR-a/b),
          no-show probability estimation, cancellation prediction, dynamic
          pricing integration. 7,000+ implementations analyzed.

SRC-T016: Behavioral Data — 14.2 billion scheduling operations analyzed
          across all platforms. Statistical findings: 73% of schedules
          modified at least once after creation. Average schedule undergoes
          47 revisions before completion or abandonment. Median reschedule
          cascade depth: 4.2 activities. Peak booking confirmation latency
          P99: 340ms. 89% of scheduling conflicts resolved by rescheduling
          (not cancellation). Average meeting scheduling negotiation
          involves 3.7 participants. 62% of workforce scheduling
          constraint violations are labor law related. No-show rates:
          healthcare 18%, restaurants 12%, personal services 15%.
          Overbooking rate: airlines 4-8%, hotels 5-15%.
```

### 0.2 Assumptions Made

```
ASM-T001: All scheduling is constraint satisfaction over temporal intervals.
          — Rationale: Analysis of SRC-T001 through SRC-T016 confirms that
            scheduling across all domains — calendaring, project management,
            workforce management, production planning, resource booking,
            transportation, healthcare, education — reduces to the same
            operation: defining activities with temporal extent, expressing
            constraints on their placement, and finding feasible assignments.
            The apparent differences are in the constraint types (labor law
            vs. manufacturing sequences vs. room capacities), not in the
            scheduling operations themselves.

ASM-T002: Optimality is a spectrum, not a binary.
          — Rationale: Feasible is not optimal. Heuristic-optimal is not
            provably optimal. Provably optimal for one objective may be
            suboptimal for another. The substrate must represent the full
            spectrum: infeasible → feasible → heuristic-optimal →
            bounded-optimal → provably optimal. Most real-world schedules
            are heuristic-optimal with no known optimality bound.
            SchedulingObjective (TERM-T024) and Schedule.quality_scores[]
            make this explicit.

ASM-T003: Schedule disruption is the normal state, not the exception.
          — Rationale: SRC-T016 shows 73% of schedules modified post-creation.
            Average 47 revisions. A substrate that treats schedule creation
            as primary and revision as exceptional is architecturally wrong.
            The primary operation is disruption handling. Schedule creation
            is a special case of disruption handling where the prior state
            is empty. Motivates Disruption (TERM-T013) and Timeline
            (TERM-T011) as first-class primitives.

ASM-T004: Timezone and calendar system diversity is baseline, not
          exceptional.
          — Rationale: 593 IANA timezone entries. Gregorian, Islamic, Hebrew,
            Chinese lunar, Japanese Imperial, Thai Buddhist, and fiscal
            calendars in active use. DST transitions occur 200+ times per
            year globally. A scheduling system that assumes a single
            timezone or calendar system is architecturally wrong. All
            internal storage is UTC with CalendarSystem reference for
            interpretation.

ASM-T005: AI agents are first-class scheduling participants.
          — Rationale: Aligns with peer substrate assumptions (ASM-G005, etc.).
            AI agents create schedules, resolve conflicts, optimize
            assignments, and manage disruptions — all within TemporalEnvelope
            constraints. They are scheduling subjects (their actions are
            scheduled) and scheduling agents (they perform scheduling
            operations). Both roles are first-class.

ASM-T006: Event sourcing is the correct persistence paradigm for
          temporal coordination.
          — Rationale: Same as all peer substrates, with an additional
            temporal-specific reason: schedule history IS the scheduling
            record. "What was the schedule on March 15?" is not a historical
            curiosity — it has operational consequences (was the SLA met?
            was the labor law violated? was the resource overbooked?).
            Only event sourcing supports time-travel queries over schedule
            state. Timeline (TERM-T011) is the immutable snapshot.

ASM-T007: The system MUST be implementable as a protocol, not only as
          a product.
          — Rationale: Same as all peer substrates, with an additional
            temporal-specific reason: scheduling is the most fragmented
            domain (175,000+ implementations). No single vendor will
            replace all scheduling tools. Interoperable implementations
            exchanging Bookings, Availability, and Schedules through a
            common protocol is the only viable path to unification.

ASM-T008: Average Booking payload is <= 2KB; average Schedule payload
          is <= 64KB.
          — Rationale: Statistical analysis of SRC-T016 (99th percentile).
            A Booking carries resource reference, time window, activity
            reference, rationale, and metadata. A Schedule carries activity
            assignments, constraint satisfaction state, and quality scores.
            Large attachments (Gantt chart renders, detailed constraint
            explanations) stored by reference in Content Store (DEP-T009).

ASM-T009: Peak global throughput is <= 20 billion temporal events per day.
          — Rationale: 14.2 billion observed operations across all platforms
            with headroom for growth. Temporal events include: booking
            created/modified/cancelled, schedule generated/revised,
            conflict detected/resolved, availability computed, disruption
            processed. The protocol must support this throughput without
            requiring all events to flow through a single system.

ASM-T010: Fairness constraints are first-class, not optimization
          preferences.
          — Rationale: Labor law (FLSA, EU Working Time Directive, French
            Code du Travail), anti-discrimination statutes, and collective
            bargaining agreements impose legally binding fairness
            requirements on scheduling. "Equitable shift distribution" is
            not a soft preference — it is a legal obligation. SchedulingPolicy
            fairness-type constraints carry legal_basis references to
            GOVERNANCE Norms. Rotation (TERM-T019) is a fairness primitive,
            not an optimization primitive.

ASM-T011: Multi-party negotiation is baseline for non-trivial scheduling.
          — Rationale: SRC-T016 shows average meeting scheduling involves
            3.7 participants. Operating room scheduling involves surgeon +
            anesthesiologist + nurses + room + equipment. Project scheduling
            involves multiple resource pools. The default case is 3+
            participants, not 1-on-1. ResourceRequirement.synchronization_mode
            addresses this.

ASM-T012: Historical schedule data improves future scheduling quality.
          — Rationale: Actual vs. estimated durations, conflict patterns,
            resource utilization rates, no-show probabilities, and cascade
            frequencies are learnable from historical data. TEMPORAL emits
            completion events; KNOWLEDGE may consume to build duration
            models. The substrate must support this feedback loop without
            requiring it.

ASM-T013: Personal schedules are sensitive data.
          — Rationale: Schedule data reveals medical appointments (health
            status), location history (movement patterns), work hours
            (employment status), meeting participants (social graph), and
            availability patterns (lifestyle). Under GDPR, this constitutes
            personal data. Under HIPAA, medical appointment schedules are
            PHI. The substrate must support granular visibility: busy/free
            without detail is the default for cross-boundary sharing.
```

### 0.3 Unknowns

```
UNK-T001: Optimal balance between schedule stability and responsiveness
          to disruption. Too-stable schedules ignore urgent changes; too-
          responsive schedules create churn that degrades human trust.
          The balance is domain-dependent: emergency departments require
          high responsiveness; construction projects require high stability.
          — Impact: SchedulingPolicy must support configurable
            disruption_response_threshold. But the optimal threshold for
            each domain is unknown and likely context-dependent.
          — Addressed by making disruption response a SchedulingPolicy
            parameter, not a system constant. Deferred to field validation.

UNK-T002: Whether scheduling fairness can be mathematically formalized
          across cultural contexts. "Fair" shift distribution means
          different things under French 35-hour law, Japanese overtime
          norms, US FLSA, and Scandinavian collective bargaining agreements.
          — Impact: SchedulingPolicy fairness-type must be parameterizable.
            Rotation (TERM-T019) must support multiple equity metrics.
          — Deferred to field validation with multiple labor law regimes.

UNK-T003: Scalability limits of constraint propagation for enterprise-
          scale schedules (10M+ activities). Airline crew scheduling
          involves millions of variable assignments. Hospital systems
          schedule millions of appointments annually.
          — Impact: Performance is implementation-dependent and solver-
            dependent. The spec defines the contract (SchedulingProblem/
            SchedulingSolution), not the solver. Solver pluggability via
            COMPUTE is the mitigation.
          — Addressed by solver interface design. Deferred to implementation.

UNK-T004: Whether stochastic scheduling (full probability distributions
          for activity durations) should be a v1 primitive or v1.1
          extension.
          — Impact: v1 supports three-point PERT estimation (min/expected/
            max). Full probability distributions would require KNOWLEDGE
            Confidence integration. Risk: premature complexity vs. missing
            a critical capability.
          — v1 uses PERT three-point. Activity carries optional
            knowledge_proposition_ref for v1.1 stochastic support.

UNK-T005: How to handle scheduling across organizations with different
          CalendarSystems and SchedulingPolicies. Cross-organization
          meeting scheduling is one of the most common scheduling
          operations and one of the hardest.
          — Impact: Cross-org scheduling must negotiate over shared
            Availability (busy/free), not shared Calendars (full detail).
            GOVERNANCE ConsentRecord governs what scheduling data is shared.
          — Addressed by Availability granular visibility. Deferred to
            implementation experience.

UNK-T006: Legal status of AI-generated schedules. Are AI-generated
          shift assignments legally binding on the employer? Can an AI
          autonomously accept patient appointments? Does an AI-generated
          production schedule constitute a commitment to delivery dates?
          — Impact: Parallels UNK-G001 (AI legal personhood). TemporalEnvelope
            limits AI scheduling authority. Legal determination is per-
            jurisdiction and evolving.
          — Deferred to GOVERNANCE integration. TemporalEnvelope is the
            mechanism; GOVERNANCE determines the normative scope.

UNK-T007: Whether quantum computing will change the tractability of
          scheduling problems. Quantum annealing has been applied to
          scheduling optimization (D-Wave). Gate-based quantum algorithms
          may improve certain constraint satisfaction problems.
          — Impact: Does not affect primitives or problem formulation. May
            affect COMPUTE integration (quantum solvers as Pipeline types).
          — Deferred to v1.1 or upon demonstrated quantum scheduling
            advantage.

UNK-T008: How to measure and compare scheduling quality across
          heterogeneous domains. A "good" airline schedule (high crew
          utilization, minimal deadheading) and a "good" hospital schedule
          (low patient wait time, equitable provider load) optimize
          different objectives.
          — Impact: SchedulingObjective (TERM-T024) is domain-configurable.
            Cross-domain quality comparison requires a meta-framework.
          — Deferred to research. SchedulingObjective provides the
            measurement infrastructure; cross-domain comparison is not
            specified.
```

---

## 1. SYSTEM INTENT (THE PROBLEM THIS SUBSTRATE SOLVES)

### 1.1 Problem Statement

Every organization coordinates activities across time. A hospital schedules
surgeries into operating rooms. An airline assigns flight crews to aircraft.
A factory sequences production orders through work centers. A university
allocates courses to classrooms and time slots. A law firm tracks filing
deadlines. A restaurant manages table reservations. A construction company
plans multi-year project timelines.

Each of these is temporal coordination: assigning activities with durations
and resource requirements to time slots, subject to constraints, with the
expectation that disruptions will occur and must be managed.

Humanity has built approximately 175,000 software implementations to solve
this problem. They share 30 recurring structural primitives. They are
mutually incompatible. A hospital that uses Epic Cadence for patient
scheduling, QGenda for physician scheduling, and Microsoft Project for
facility construction planning maintains three separate temporal
coordination systems with no shared model of time, availability, or
conflict.

SUBSTRATE-TEMPORAL extracts the 30 universal primitives, defines their
relationships, and specifies a single protocol for temporal coordination
across all domains.

### 1.2 Actors

```
ACT-T001: Human Scheduler
          Goal:        Create, modify, and monitor schedules within authority.
          Trust level: Trusted for scheduling decisions within delegated scope.
                       May override AI recommendations with justification.
          Constraints: Bounded by SchedulingPolicy. Must provide rationale for
                       constraint relaxation.

ACT-T002: Temporal Steward
          Goal:        Configure organizational temporal structure — calendars,
                       policies, cadences, shift patterns, resource pools.
          Trust level: Highest human authority for temporal configuration.
                       Configures SchedulingPolicies, defines CalendarSystems,
                       establishes organizational Cadences.
          Constraints: Configuration changes require audit trail. Cannot override
                       GOVERNANCE compliance constraints.

ACT-T003: AI Agent (Narrow Temporal)
          Goal:        Execute bounded scheduling tasks within TemporalEnvelope.
          Trust level: Trusted for routine scheduling within envelope limits.
                       May create/modify Bookings, detect Conflicts, propose
                       Resolutions. May NOT relax hard constraints or override
                       human scheduling decisions.
          Constraints: TemporalEnvelope defines maximum horizon, booking limits,
                       accessible resource pools, conflict resolution authority.

ACT-T004: AI Agent (General Temporal)
          Goal:        Cross-domain scheduling optimization with expanded
                       TemporalEnvelope.
          Trust level: Trusted for complex multi-domain scheduling. May propose
                       constraint relaxation. May NOT approve constraint
                       relaxation on hard constraints without human authority.
          Constraints: Expanded TemporalEnvelope. Still bounded by GOVERNANCE
                       compliance constraints. All optimization decisions
                       auditable via scheduling_rationale.

ACT-T005: Human Participant (Internal)
          Goal:        View own schedule, declare preferences, accept/decline
                       Bookings, report scheduling conflicts.
          Trust level: Trusted for own availability and preferences. Not
                       trusted for organizational scheduling decisions.
          Constraints: May view own schedule and busy/free of colleagues
                       (per access policy). May declare preferences but
                       not enforce them as hard constraints.

ACT-T006: External System
          Goal:        Exchange temporal data with SUBSTRATE-TEMPORAL.
          Trust level: Varies by integration contract. Calendar sync (iCalendar)
                       is read-only import. Solver execution (COMPUTE) is
                       trusted for computational results. ERP integration is
                       trusted for demand signals.
          Constraints: Must conform to integration contract schemas. Data
                       validated on ingestion. No direct schedule modification
                       without mapping to TEMPORAL primitives.

ACT-T007: Auditor (Temporal)
          Goal:        Verify scheduling compliance, analyze efficiency, detect
                       systematic bias in scheduling decisions.
          Trust level: Read-only access to all scheduling data including
                       scheduling_rationale, constraint relaxation history, and
                       fairness metrics.
          Constraints: Cannot modify schedules. Audit findings reported via
                       GOVERNANCE ComplianceAssessment.

ACT-T008: Human Participant (External)
          Goal:        Interact with scheduling as a service consumer — book
                       appointments, join waitlists, view available time slots.
          Trust level: Untrusted for scheduling decisions. Trusted for own
                       identity and stated preferences only.
          Constraints: Sees only public availability (busy/free without internal
                       detail). Cannot view other participants' schedules.
                       Rate-limited to prevent abuse.
```

### 1.3 Non-Goals

```
NG-T001: SUBSTRATE-TEMPORAL is NOT a scheduling solver.
         Solvers (CP-SAT, MILP, genetic algorithms, custom heuristics) plug
         in via COMPUTE Pipelines (INT-T002). TEMPORAL defines the problem
         (SchedulingProblem schema); COMPUTE runs the solver; TEMPORAL
         consumes the solution (SchedulingSolution schema). The substrate
         is solver-agnostic.

NG-T002: SUBSTRATE-TEMPORAL does NOT replace calendar user interfaces or
         Gantt chart renderers.
         Presentation is external. TEMPORAL provides the data model and
         protocol; rendering as calendar views, Gantt charts, timeline
         visualizations, shift boards, or booking grids is the
         responsibility of consuming applications.

NG-T003: SUBSTRATE-TEMPORAL does NOT own financial aspects of scheduling.
         Overtime rates, premium pay calculations, penalty costs, booking
         revenue, and cancellation fees are BUSINESS computations. TEMPORAL
         provides the temporal allocation data (who worked when, what was
         booked when). BUSINESS computes costs. Parallels the DESIGN-
         BUSINESS boundary for manufacturing cost estimation.

NG-T004: SUBSTRATE-TEMPORAL does NOT own operational/real-time timing.
         PHYSICAL handles control loops, safety functions, and equipment
         operation regardless of duration. TEMPORAL handles planning,
         coordination, and resource allocation regardless of duration.
         Purpose, not duration, is the boundary. A 200ms booking
         confirmation is TEMPORAL (coordination). A 200ms safety interlock
         is PHYSICAL (control). A 30-year maintenance lifecycle plan is
         TEMPORAL (planning). A 30-year continuous monitoring system is
         PHYSICAL (sensing).

NG-T005: SUBSTRATE-TEMPORAL does NOT define domain-specific calendar
         content.
         National holidays, business hours, academic terms, shift patterns,
         and maintenance windows are configuration data loaded by ACT-T002
         (Temporal Steward). The substrate provides the container (Calendar,
         CalendarSystem); the content is organizational.

NG-T006: SUBSTRATE-TEMPORAL does NOT enforce governance constraints
         directly.
         GOVERNANCE defines labor law norms with structured
         temporal_constraint_spec. TEMPORAL applies them as SchedulingPolicy
         compliance-type constraints. TEMPORAL reports violations as events.
         GOVERNANCE determines consequences. Principle P3: GOVERNANCE
         defines; TEMPORAL applies; GOVERNANCE enforces.

NG-T007: SUBSTRATE-TEMPORAL does NOT perform resource procurement.
         When scheduling reveals insufficient capacity (not enough nurses,
         not enough machines, not enough rooms), TEMPORAL reports the gap
         via Capacity analysis. BUSINESS handles hiring, purchasing, or
         renting additional resources. TEMPORAL consumes the updated
         resource pool.
```

### 1.4 Success Criteria

```
SUCCESS-T001: Any scheduling operation expressible in any of the 175,000+
              analyzed implementations can be expressed as a composition
              of TEMPORAL primitives without loss of scheduling semantics.

SUCCESS-T002: A Schedule produced by any pluggable solver via COMPUTE
              can be validated against all Constraints, Dependencies, and
              SchedulingPolicies without knowledge of the solver's internal
              algorithm.

SUCCESS-T003: Disruption handling — from detection through cascade analysis
              through rescheduling recommendation through resolution — is
              a first-class operation with explicit state tracking, not an
              ad-hoc modification of existing Bookings.

SUCCESS-T004: Scheduling fairness is measurable and auditable. For any
              SchedulableResource pool with fairness-type SchedulingPolicy,
              an Auditor (ACT-T007) can determine whether scheduling
              decisions exhibit systematic bias.

SUCCESS-T005: Cross-substrate scheduling compositions (project management
              = BUSINESS + TEMPORAL, production scheduling = DESIGN +
              TEMPORAL + BUSINESS, meeting scheduling = TEMPORAL +
              COMMUNICATION) produce coherent results without requiring
              any substrate to duplicate another's primitives.
```

### 1.5 Failure Criteria

```
FAILURE-T001: If the system cannot express a scheduling constraint that
              exists in any of the 16 source categories, the primitive set
              is incomplete.

FAILURE-T002: If a Schedule that satisfies all Constraints but fails human
              acceptance testing (because it ignores perception asymmetry
              or fairness), the SchedulingPolicy model is insufficient.

FAILURE-T003: If disruption handling requires manual reconstruction of
              schedule state rather than operating on explicit Disruption
              and Timeline primitives, the disruption model has failed.

FAILURE-T004: If scheduling across two substrates (e.g., TEMPORAL +
              PHYSICAL for maintenance scheduling) requires inventing
              ad-hoc integration rather than using defined integration
              contracts, the cross-substrate model has failed.

FAILURE-T005: If an AI agent can schedule resources beyond its
              TemporalEnvelope without detection and prevention, the
              authority model has failed.
```

---

## 2. SYSTEM BOUNDARIES

### 2.1 Dependencies

```
DEP-T001: CROSS-SUBSTRATE-CONVENTIONS v1.4+
          — Shared envelope chain, event schema, cross-substrate references,
            primitive ownership table, naming conventions. TEMPORAL is the
            eighth substrate in the envelope chain.

DEP-T002: SUBSTRATE-BUSINESS v2+
          — Entity (organizational structure), Workflow (lifecycle management),
            Reservation (TERM-023, commercial agreement referencing Booking),
            Schedule trigger (TERM-017, time-based trigger referencing
            Recurrence). TEMPORAL provides temporal allocation; BUSINESS
            provides commercial context.

DEP-T003: SUBSTRATE-KNOWLEDGE v1+
          — Proposition (TERM-K001, for duration estimates and demand
            forecasts), Confidence (TERM-K003, for estimation uncertainty),
            Argument (TERM-K015, for scheduling rationale chains).
            TEMPORAL consumes knowledge for planning parameters; emits
            completion data for knowledge updates.

DEP-T004: SUBSTRATE-COMPUTE v1+
          — Pipeline (TERM-C003, for solver execution), Dataset (TERM-C004,
            SchedulingProblem as input), Result (TERM-C005, SchedulingSolution
            as output), Resource (TERM-C002, solver infrastructure).
            TEMPORAL defines the problem; COMPUTE runs the solver.

DEP-T005: SUBSTRATE-COMMUNICATION v1+
          — Discourse (TERM-M001, for meeting content after scheduling),
            Commitment (TERM-M005, deadlines triggering TEMPORAL Deadlines),
            SpeechAct (TERM-M002, for booking acceptance/decline).
            TEMPORAL schedules the time; COMMUNICATION fills it with
            discourse.

DEP-T006: SUBSTRATE-PHYSICAL v1+
          — PhysicalAsset (TERM-P003, state feeds Availability),
            ProcessExecution (TERM-P012, maintenance execution after
            TEMPORAL scheduling), MaintenanceAction (TERM-P021,
            calibration/repair after TEMPORAL scheduling).
            PHYSICAL state drives TEMPORAL availability; TEMPORAL
            schedules PHYSICAL maintenance.

DEP-T007: SUBSTRATE-DESIGN v1+
          — DesignReview (TERM-D022, scheduling requested via event),
            BOM (TERM-D021, production schedule input),
            FabricationMethod (TERM-D020, process sequence input).
            DESIGN provides what to build; TEMPORAL provides when to
            build it.

DEP-T008: SUBSTRATE-GOVERNANCE v1+
          — Norm (TERM-G001, labor law norms with temporal_constraint_spec),
            Obligation (TERM-G005, SLA obligations referencing
            TemporalServiceMetric), ConsentRecord (TERM-G027, scheduling
            data sharing consent), GovernanceEnvelope (TERM-G026,
            compliance constraints on scheduling).
            GOVERNANCE constrains; TEMPORAL complies and measures.

DEP-T009: Content Store (shared infrastructure)
          — Storage for large schedule attachments, recurring pattern
            libraries, solver configuration files, and detailed constraint
            explanations that exceed the 64KB Schedule payload limit
            (ASM-T008). Referenced by content_ref fields. Same Content
            Store used by all peer substrates.
```

### 2.2 Explicit Exclusions

```
EXCL-T001: Domain-specific scheduling solver algorithms.
           — Excluded per NG-T001. Solvers are COMPUTE Pipelines.
             The substrate defines the problem format, not the solution
             algorithm.

EXCL-T002: Calendar and scheduling user interface rendering.
           — Excluded per NG-T002. Gantt charts, calendar views, shift
             boards, and timeline visualizations are presentation concerns.

EXCL-T003: Financial cost computation for scheduling decisions.
           — Excluded per NG-T003. Overtime costs, premium pay, booking
             revenue, and penalty calculations are BUSINESS operations.

EXCL-T004: Real-time control loop timing.
           — Excluded per NG-T004. Control loops, safety interlocks, and
             equipment operation timing are PHYSICAL, regardless of
             duration. Purpose is the boundary.

EXCL-T005: ERP/MRP production planning (full scope).
           — TEMPORAL owns the scheduling logic (Activity sequencing,
             resource assignment, constraint satisfaction). BUSINESS owns
             demand management, cost optimization, and procurement.
             DESIGN owns BOM and process definition. Full ERP/MRP is a
             three-substrate composition, not a single-substrate feature.
             References NG-D004 in DESIGN.

EXCL-T006: Calendar content curation.
           — Excluded per NG-T005. Holiday lists, business hour definitions,
             and academic term dates are configuration data, not substrate
             primitives.
```

### 2.3 Trust Boundaries

```
TRUST-T001: Internal Participants vs. External Participants.
            — Internal participants (ACT-T005) see their own full schedule
              and busy/free of colleagues per access policy. External
              participants (ACT-T008) see only public availability slots.
              Internal scheduling rationale, constraint details, and
              resource assignments are never exposed to external
              participants. This is the primary privacy boundary.

TRUST-T002: Human Schedulers vs. AI Agents.
            — Human Schedulers (ACT-T001) may relax hard constraints with
              justification. AI Agents (ACT-T003, ACT-T004) may NOT relax
              hard constraints without human approval. AI Agents operate
              within TemporalEnvelope. All AI scheduling decisions carry
              scheduling_rationale for auditability.

TRUST-T003: Scheduling Authority vs. Audit Authority.
            — Schedulers (ACT-T001, ACT-T003, ACT-T004) create and modify
              schedules. Auditors (ACT-T007) have read-only access to all
              scheduling data including rationale and fairness metrics.
              Auditors cannot modify schedules. Separation of scheduling
              and audit authority is mandatory.

TRUST-T004: Cross-Organization Scheduling.
            — Organizations share Availability (busy/free) for cross-org
              scheduling. They do NOT share Calendar details, Activity
              descriptions, or scheduling rationale. Availability
              granularity (busy/free vs. tentative/available vs. full
              detail) is controlled by GOVERNANCE ConsentRecord. Default
              is busy/free only.

TRUST-T005: Solver Trust.
            — Scheduling solvers execute via COMPUTE Pipelines. Solver
              output (SchedulingSolution) is validated by TEMPORAL against
              all Constraints and Dependencies before acceptance. A solver
              cannot produce an accepted Schedule that violates a hard
              Constraint. Solver validation is mandatory, not optional.
```

### 2.4 Network Boundaries

```
NETWORK-T001: TEMPORAL operates within the cross-substrate event mesh
              defined by CROSS-SUBSTRATE-CONVENTIONS Section 3. All
              temporal events use the `substrate.temporal.*` topic
              namespace. Events cross substrate boundaries only through
              the event mesh — no direct substrate-to-substrate calls
              for temporal operations.

NETWORK-T002: Cross-organization scheduling uses Availability exchange
              over the event mesh with TRUST-T004 visibility controls.
              No direct access to another organization's Calendar,
              Activity, or Booking data.

NETWORK-T003: Solver invocation uses COMPUTE Pipeline execution. The
              SchedulingProblem is submitted as a COMPUTE Dataset. The
              SchedulingSolution is returned as a COMPUTE Result. No
              direct TEMPORAL-to-solver communication outside the
              COMPUTE protocol.
```

### 2.5 Runtime Boundaries

```
RUNTIME-T001: TEMPORAL is an event-sourced system. All state changes
              (Booking created, Schedule revised, Conflict detected,
              Disruption processed) produce immutable events. Current
              state is derived from the event stream. Timeline (TERM-T011)
              is the immutable snapshot mechanism.

RUNTIME-T002: Scheduling operations are eventually consistent. A Booking
              created in one partition is visible to other partitions
              within the consistency window. Double-booking prevention
              uses optimistic concurrency with conflict detection on
              resource-timewindow pairs (CONC-T001).

RUNTIME-T003: TEMPORAL does not impose real-time latency guarantees on
              scheduling operations. Booking confirmation latency is
              implementation-dependent. The spec defines correctness
              constraints (no double-booking, all hard constraints
              satisfied), not latency targets. Latency targets are
              operational configuration per TemporalServiceMetric.
```

---

## 3. GLOSSARY (PRIMITIVES)

> Every term below is a first-class entity in SUBSTRATE-TEMPORAL.
> Identifiers follow the pattern TERM-T###. Cross-substrate relationships
> reference TERM identifiers from peer substrates. Principle references
> (P1–P4) refer to CROSS-SUBSTRATE-CONVENTIONS Section 6.

### Category A — Temporal Containers & Interpretation

```
TERM-T001: Calendar
           A named, timezone-aware temporal container defining working
           periods, exceptions, and scheduling context within a scope.
           — Has: calendar_id (UUID), organization_id, name, description,
             calendar_system_ref (CalendarSystem TERM-T027 ref),
             default_timezone (IANA tz identifier), working_periods[]
             (recurring TimeWindow refs defining normal availability),
             exceptions[] ({exception_id, name, date_range, override_type
             (enum: holiday, shutdown, maintenance_window, special_hours,
             custom), scope (enum: organization, department, resource,
             location), availability_override (available/unavailable/
             modified_hours), recurrence_ref (nullable — Recurrence
             TERM-T005 for annual holidays)}), parent_calendar_ref
             (nullable — for hierarchical calendar inheritance),
             scope (enum: organization, department, team, individual,
             resource_pool, location), status (enum: active, archived),
             version, created_at, created_by.
           — The foundational temporal container. Every SchedulableResource
             references at least one Calendar. Working periods define
             normal availability (e.g., Mon-Fri 9AM-5PM). Exceptions
             override normal availability with typed reasons: a holiday
             closes the office, a maintenance window blocks a machine,
             special hours extend availability for an event.
           — Calendar inheritance: a resource inherits its department
             Calendar, which inherits the organization Calendar. Exceptions
             at lower scopes override higher scopes. This mirrors
             organizational hierarchy without duplicating temporal data.
           — Cross-substrate: BUSINESS Organization (TERM-001) structure
             informs Calendar scope hierarchy. Calendar does NOT duplicate
             organizational structure — it references it. Principle P4.

TERM-T002: TimeWindow
           A bounded interval [start, end) with optional recurrence,
           timezone context, and availability state.
           — Has: window_id (UUID), start (UTC timestamp), end (UTC
             timestamp, exclusive), timezone (IANA tz identifier for
             display), duration (computed: end - start), availability_state
             (enum: available, unavailable, tentative, conditional,
             on_call, standby), recurrence_ref (nullable — Recurrence
             TERM-T005 ref if this window repeats), conditions[]
             (nullable — for conditional availability: what conditions
             must hold), response_time (nullable — for on_call state:
             maximum response time if activated), activation_conditions
             (nullable — for standby state: what triggers activation),
             metadata{}.
           — The atomic temporal unit. All scheduling operates on
             TimeWindows. [start, end) is half-open: start is inclusive,
             end is exclusive. This eliminates ambiguity at boundaries
             (a meeting ending at 3:00 PM and one starting at 3:00 PM
             do not overlap).
           — Availability states beyond binary (available/unavailable):
             tentative = provisionally held, may be displaced; conditional
             = available if conditions are met; on_call = not actively
             working but must respond within response_time; standby =
             available for activation under specific conditions. These
             states reflect real-world scheduling complexity (healthcare
             on-call, airline standby crews, conditional equipment
             availability).
           — Cross-substrate: TimeWindow is the temporal primitive that
             other substrates reference when they need to express "during
             this period." BUSINESS Schedule trigger (TERM-017) references
             TimeWindow for its temporal extent. PHYSICAL MaintenanceAction
             execution window maps to a TimeWindow.

TERM-T003: Availability
           The computed set of TimeWindows during which a SchedulableResource
           can accept Bookings, derived from Calendar rules, existing
           Bookings, Constraints, and capacity levels.
           — Has: availability_id (UUID), resource_ref (SchedulableResource
             TERM-T016 ref), computed_at (UTC timestamp), horizon_ref
             (Horizon TERM-T012 ref — how far into the future),
             windows[] (TimeWindow refs with available capacity per window),
             capacity_per_window[] ({window_ref, total_capacity,
             committed_capacity, available_capacity, unit_type}),
             computation_inputs ({calendar_refs[], booking_refs[],
             constraint_refs[], capacity_ref}), visibility_level (enum:
             full_detail, busy_free, slots_only), cache_ttl (duration —
             how long this computation remains valid).
           — Availability is COMPUTED, not declared. It is the result of
             subtracting existing Bookings from Calendar working periods,
             applying Constraints, and accounting for capacity levels.
             A conference room with capacity 1 is unavailable when booked.
             A doctor with capacity 4 (four concurrent patients) is
             available at reduced capacity when 3 are booked.
           — Visibility levels enforce TRUST-T001: full_detail shows
             what is booked and by whom; busy_free shows only occupied
             vs. open; slots_only shows bookable time slots without
             context. Default for cross-organization: busy_free.
           — Not just binary: partial capacity support is critical for
             degraded equipment (PHYSICAL), reduced staffing, and shared
             resources with multiple concurrent use.

TERM-T005: Recurrence
           A declarative rule generating repeating TimeWindows or Bookings.
           — Has: recurrence_id (UUID), rule (RFC 5545 RRULE string or
             extended syntax), effective_from (UTC timestamp), effective_until
             (nullable — UTC timestamp), exception_dates[] (EXDATE list —
             specific dates excluded from the pattern), exception_rules[]
             (EXRULE list — pattern-based exclusions), extensions
             ({rotating_shift (nullable — rotation pattern for workforce),
             academic_term (nullable — term/semester structure),
             fiscal_period (nullable — fiscal quarter/year structure)}),
             generated_count (computed — how many instances generated to
             date), next_occurrence (computed — next future instance),
             created_at, created_by.
           — Supports full RFC 5545 RRULE semantics: FREQ (YEARLY, MONTHLY,
             WEEKLY, DAILY, HOURLY, MINUTELY, SECONDLY), INTERVAL, COUNT,
             UNTIL, BYDAY, BYMONTH, BYMONTHDAY, BYHOUR, BYMINUTE,
             BYSECOND, BYSETPOS, WKST. Plus extensions for patterns RFC
             5545 cannot express: rotating shifts (ABAB, 4-on-2-off),
             academic terms (variable-length with mid-term breaks), and
             fiscal periods (4-4-5, 4-5-4, 5-4-4 week patterns).
           — TEMPORAL is the sole owner of RFC 5545 RRULE interpretation.
             BUSINESS TERM-017 Schedule trigger's recurring type
             (`every P per RFC 5545`) delegates RRULE interpretation to
             TEMPORAL Recurrence. COMPUTE TERM-C007 Schedule's one-shot
             and recurring types delegate temporal logic to TEMPORAL
             TimeWindow and Recurrence. Principle P4: one owner per
             concept.

TERM-T027: CalendarSystem
           A named set of rules for interpreting dates, months, years,
           epochs, AND timezone offset rules including DST transitions.
           — Has: calendar_system_id (UUID), name, type (enum: gregorian,
             islamic_hijri, hebrew, chinese_lunar, japanese_imperial,
             thai_buddhist, fiscal_custom, iso_week), epoch_definition
             (the reference point for year numbering), month_rules
             (how months are determined — solar, lunar, lunisolar),
             leap_rules (when leap days/months are inserted),
             week_rules ({first_day_of_week, min_days_in_first_week,
             weekend_days[]}), timezone_rules_ref (IANA tz database
             reference — includes all DST transition rules, historical
             timezone changes, leap second handling), display_format
             (locale-specific date/time formatting), created_at,
             created_by.
           — Subsumes timezone interpretation. Timezone is an attribute
             of temporal interpretation, not an independent entity. All
             internal storage is UTC + CalendarSystem reference for
             interpretation. A CalendarSystem with type=gregorian and
             timezone_rules_ref=America/New_York produces Eastern Time
             interpretation. A CalendarSystem with type=islamic_hijri
             and timezone_rules_ref=Asia/Riyadh produces Hijri calendar
             in Arabia Standard Time.
           — Property T1 motivation: "3 PM Tuesday" requires knowing
             the CalendarSystem to determine the UTC instant. The same
             CalendarSystem may produce different UTC instants on
             different dates due to DST transitions. Leap seconds,
             while rare, affect precise scheduling (satellite operations,
             financial trading). The CalendarSystem encapsulates all
             this complexity behind a single reference.
           — Cross-substrate: All substrates that reference timestamps
             use UTC. CalendarSystem is TEMPORAL-owned interpretation
             logic. Other substrates do not need to know about timezone
             rules — they store UTC and reference TEMPORAL CalendarSystem
             when human-readable interpretation is needed.
```

### Category B — Activities & Structure

```
TERM-T007: Activity
           A unit of schedulable work with duration, resource requirements,
           temporal constraints, and priority.
           — Has: activity_id (UUID), organization_id, name, description,
             activity_type (enum: task, meeting, appointment, maintenance,
             production, examination, hearing, event, training, travel,
             custom), duration ({type (enum: fixed, estimated, range),
             value (ISO 8601 duration for fixed), min (duration for
             estimated/range), expected (duration for estimated), max
             (duration for estimated/range)}), resource_requirements[]
             (ResourceRequirement TERM-T017 refs), constraints[]
             (Constraint TERM-T006 refs), dependencies[] (Dependency
             TERM-T009 refs), priority (integer, lower = higher priority),
             deadline_ref (nullable — Deadline TERM-T020 ref),
             schedule_ref (Schedule TERM-T010 ref), scheduling_rationale
             (text — why this resource/time was assigned; supports bias
             auditing ACT-T007), knowledge_proposition_ref (nullable —
             KNOWLEDGE Proposition TERM-K001 ref for v1.1 stochastic
             duration), status (per SM-T001), actual_start (nullable —
             UTC timestamp), actual_end (nullable — UTC timestamp),
             actual_duration (computed from actuals), metadata{},
             tags[], created_at, created_by.
           — Duration types: fixed = exact duration known (1-hour meeting).
             estimated = three-point PERT estimate (min/expected/max)
             for planning under uncertainty. range = bounded but no
             expected value (between 2 and 4 hours). Estimated durations
             enable probabilistic schedule analysis without requiring
             full stochastic modeling (deferred to v1.1 via
             knowledge_proposition_ref).
           — scheduling_rationale is a first-class field, not optional
             metadata. Every scheduling decision must be explainable.
             This supports bias auditing (Property T9), regulatory
             compliance (GOVERNANCE), and human trust in AI-generated
             schedules.
           — Cross-substrate: Activity is TEMPORAL's core schedulable unit.
             BUSINESS Entity (TERM-001) lifecycle events may trigger
             Activity creation (e.g., order received → schedule production).
             COMMUNICATION Discourse (TERM-M001) may be associated with
             a meeting-type Activity. PHYSICAL ProcessExecution (TERM-P012)
             may be the execution of a maintenance-type Activity.

TERM-T008: Milestone
           A zero-duration marker representing a significant schedule point.
           — Has: milestone_id (UUID), organization_id, name, description,
             milestone_type (enum: deadline, handoff, gate, delivery,
             phase_boundary, contractual, regulatory, custom),
             target_date (UTC timestamp), schedule_ref (Schedule TERM-T010
             ref), dependencies[] (Dependency TERM-T009 refs),
             status (enum: pending, achieved, missed, deferred),
             achieved_date (nullable — actual date achieved),
             variance (computed — target_date minus achieved_date),
             escalation_rules[] (nullable — what happens if missed),
             source_ref (nullable — cross-substrate reference to the
             origin: BUSINESS deliverable, GOVERNANCE deadline,
             COMMUNICATION commitment), created_at, created_by.
           — Zero-duration is the defining characteristic. Milestones
             constrain the schedule without consuming resources. A
             project deadline, a regulatory filing date, a contractual
             delivery date, and a phase gate review are all Milestones.
           — Distinguished from Deadline (TERM-T020): a Milestone is a
             schedule marker; a Deadline is a temporal bound with
             escalation semantics. A Milestone MAY have a corresponding
             Deadline. Not all Milestones are Deadlines (a phase boundary
             is a Milestone but may not have escalation rules).

TERM-T009: Dependency
           A typed directed link between Activities specifying sequencing
           with optional lag or lead time.
           — Has: dependency_id (UUID), predecessor_ref (Activity TERM-T007
             ref), successor_ref (Activity TERM-T007 ref), type (enum:
             FS (finish-to-start), SS (start-to-start), FF (finish-to-
             finish), SF (start-to-finish)), lag (nullable — ISO 8601
             duration; positive = lag, negative = lead), constraint_type
             (enum: hard, soft), description, created_at, created_by.
           — Strictly Activity-to-Activity sequencing in the CPM/PERT
             tradition. FS: successor starts after predecessor finishes
             (most common). SS: successor starts after predecessor starts.
             FF: successor finishes after predecessor finishes. SF:
             successor starts before predecessor finishes.
           — Distinguished from Constraint (TERM-T006): Dependencies are
             sequencing links between Activities. Constraints are all
             other temporal relationships (overlaps, simultaneous, mutex,
             proximity). A Dependency that can be expressed as a Constraint
             SHOULD be modeled as a Dependency for CPM/PERT compatibility
             (critical path analysis requires explicit sequencing links).
           — Lag/lead: lag = mandatory wait time between linked activities
             (concrete curing: FS + 24h lag). Lead = overlap allowed
             (start successor before predecessor completes: FS - 2h lead).

TERM-T006: Constraint
           A temporal relationship between Activities or TimeWindows beyond
           sequencing.
           — Has: constraint_id (UUID), organization_id, name, description,
             constraint_type (enum: overlaps, simultaneous, mutex,
             proximity, time_fence, resource_leveling, custom),
             participants[] (Activity and/or TimeWindow refs),
             hardness (enum: hard, soft, preference),
             violation_penalty (nullable — numeric cost of violating a
             soft constraint; used by solver for optimization),
             relaxation_priority (nullable — integer; order in which to
             relax constraints when infeasible; lower = relax last),
             relaxed_by (nullable — Resolution TERM-T015 ref if this
             constraint was relaxed), parameters ({proximity_min
             (nullable — minimum gap), proximity_max (nullable — maximum
             gap), time_fence_start (nullable), time_fence_end (nullable),
             leveling_threshold (nullable)}), source_ref (nullable —
             cross-substrate reference: GOVERNANCE Norm for compliance
             constraints, PHYSICAL safety requirement, etc.),
             status (enum: active, relaxed, suspended, archived),
             created_at, created_by.
           — Constraint types: overlaps = activities must overlap in time.
             simultaneous = activities must start and end together.
             mutex = activities must NOT overlap (mutual exclusion on a
             resource). proximity = activities must be within min/max
             time of each other. time_fence = activities frozen within
             a time window (no rescheduling allowed). resource_leveling
             = resource usage must not exceed threshold.
           — Hardness model: hard = must be satisfied; solver fails if
             violated. soft = should be satisfied; violation incurs
             penalty cost in objective function. preference = nice to
             have; lowest-priority relaxation candidate.
           — Constraint relaxation: when no feasible Schedule exists,
             soft and preference Constraints are relaxed in
             relaxation_priority order until feasibility is achieved.
             Each relaxation creates a Resolution (TERM-T015) record
             with justification. Hard Constraints are NEVER automatically
             relaxed — infeasibility with only hard Constraints remaining
             requires human intervention.
           — Cross-substrate: GOVERNANCE Norms with temporal_constraint_spec
             become TEMPORAL Constraints with source_ref pointing to the
             Norm. Labor law "minimum 11 hours rest between shifts" is a
             Constraint with constraint_type=proximity, hardness=hard,
             and source_ref → GOVERNANCE Norm. Principle P3.

TERM-T020: Deadline
           A temporal bound on Activity or Milestone completion with
           escalation semantics.
           — Has: deadline_id (UUID), target_ref (Activity TERM-T007 or
             Milestone TERM-T008 ref), due (UTC timestamp), type (enum:
             hard, soft), escalation_rules[] ({trigger_offset (duration
             before/after due), action (enum: notify, warn, escalate,
             block, auto_cancel), recipients[] (agent_ids or roles),
             message_template}), notification_triggers[]
             ({offset (duration before due), channel, recipients[]}),
             source_ref (nullable — cross-substrate reference:
             COMMUNICATION Commitment TERM-M005 deadline,
             GOVERNANCE Obligation TERM-G005 deadline, BUSINESS
             deliverable deadline, legal filing deadline), status (enum:
             pending, approaching, met, breached, waived),
             breach_timestamp (nullable), created_at, created_by.
           — A specialized primitive for a universal pattern. Deadlines
             exist in every scheduling domain. The escalation semantics
             justify separation from Constraint: a Constraint says
             "activity must complete by T"; a Deadline says "activity
             must complete by T, and if it doesn't, notify these people
             at T-24h, escalate to management at T-1h, and block
             dependent work at T."
           — Analogous to GOVERNANCE separating Obligation (TERM-G005)
             from Norm (TERM-G001): the normative content (complete by
             T) is distinct from the lifecycle management (escalation,
             notification, breach recording).
           — Cross-substrate: TEMPORAL is the authoritative deadline
             tracker. COMMUNICATION Commitment.deadline may trigger
             creation of a TEMPORAL Deadline with source_ref. GOVERNANCE
             Obligation.deadline may trigger creation of a TEMPORAL
             Deadline with source_ref. Single authoritative tracking
             point; event-driven propagation. Principle P4.
```

### Category C — Scheduling & Plans

```
TERM-T010: Schedule
           A consistent assignment of Activities to TimeWindows and
           Resources satisfying all Constraints and Dependencies.
           — Has: schedule_id (UUID), organization_id, name, description,
             schedule_type (enum: project, workforce, production,
             appointment, resource_booking, maintenance, custom),
             horizon_ref (Horizon TERM-T012 ref), activities[]
             (Activity TERM-T007 refs), dependencies[] (Dependency
             TERM-T009 refs), constraints[] (Constraint TERM-T006 refs),
             bookings[] (Booking TERM-T004 refs — the resource
             assignments), milestones[] (Milestone TERM-T008 refs),
             feasibility_status (enum: feasible, infeasible, relaxed),
             quality_scores[] ({objective_ref (SchedulingObjective
             TERM-T024 ref), score (numeric), unit}),
             optimality_bound (nullable — solver-provided bound on
             solution quality; null if heuristic with no bound),
             comparison_baseline_ref (nullable — Timeline TERM-T011 ref
             for before/after comparison), solver_ref (nullable —
             COMPUTE Pipeline ref that produced this schedule),
             policies[] (SchedulingPolicy TERM-T026 refs applied),
             status (per SM-T003), version (integer, monotonically
             increasing), created_at, created_by, last_modified_at.
           — The central coordination artifact. A Schedule is not a
             calendar view or a Gantt chart (NG-T002). It is the
             constraint-satisfaction result: the assignment of activities
             to time slots and resources that satisfies all constraints.
           — feasibility_status: feasible = all constraints satisfied.
             infeasible = hard constraints cannot all be satisfied (requires
             human intervention). relaxed = feasible only after relaxing
             some soft constraints (Resolution records explain which
             constraints were relaxed and why).
           — NOTE: Name collision with BUSINESS TERM-017 (ScheduleTrigger).
             TEMPORAL Schedule = constraint-satisfaction result. BUSINESS
             Schedule = time-based trigger. Different concepts sharing a
             name. Disambiguated in CROSS-SUBSTRATE-CONVENTIONS Section 7
             Ownership Table.

TERM-T011: Timeline
           An ordered, immutable snapshot of a Schedule at a point in time.
           — Has: timeline_id (UUID), schedule_ref (Schedule TERM-T010 ref),
             snapshot_timestamp (UTC — when this snapshot was taken),
             version (integer — corresponds to Schedule.version),
             activity_assignments[] ({activity_ref, timewindow, resource_ref,
             status_at_snapshot}), constraint_satisfaction_state[]
             ({constraint_ref, satisfied (boolean), relaxed (boolean)}),
             critical_path[] (computed — ordered Activity refs on the
             longest dependency chain), slack_per_activity[]
             ({activity_ref, total_slack (duration), free_slack (duration)}),
             delta_from_previous (nullable — structured diff from prior
             Timeline: activities added/removed/moved, resources changed,
             constraints relaxed/restored), hash (integrity hash of
             snapshot contents), created_at.
           — Immutability is the defining characteristic. Once created, a
             Timeline is never modified. Schedule revision creates a new
             Timeline; the old one persists for comparison, audit, and
             historical analysis.
           — CriticalPath and Slack are computed properties of Timeline,
             not separate primitives. The critical path is the longest
             chain of dependent activities; slack is the amount each
             non-critical activity can shift without affecting the critical
             path. Both are meaningful only in the context of a specific
             schedule snapshot.
           — Enables "what changed" analysis: comparing two Timelines
             reveals exactly which activities moved, which resources were
             reassigned, and which constraints were relaxed. This is
             the event-sourcing dividend for scheduling (ASM-T006).

TERM-T012: Horizon
           The temporal boundary of a Schedule — how far into the future
           it extends and at what resolution.
           — Has: horizon_id (UUID), start (UTC timestamp), end (UTC
             timestamp), type (enum: operational, tactical, strategic),
             resolution ({granularity (enum: minute, hour, day, week,
             month, quarter), scheduling_precision (duration — minimum
             schedulable time unit)}), rolling_window (nullable — if
             true, horizon advances with time: {advance_frequency
             (duration), advance_amount (duration)}), update_frequency
             (duration — how often the schedule within this horizon is
             re-optimized), created_at, created_by.
           — Horizon types: operational = days to weeks, minute/hour
             resolution (today's OR schedule, this week's shift roster).
             tactical = weeks to months, day/week resolution (this
             quarter's project plan, next month's maintenance schedule).
             strategic = months to years, week/month/quarter resolution
             (annual capacity plan, multi-year project portfolio).
           — Resolution determines schedulable precision. A strategic
             horizon with monthly resolution does not schedule to the
             minute. An operational horizon with minute resolution does
             not extend to next year. This prevents inappropriate
             precision (scheduling a meeting room for 2027 at 3:17 PM).
           — Property T6 motivation: TEMPORAL spans sub-second to
             multi-decade. Horizon ensures each Schedule operates at
             appropriate resolution for its purpose.

TERM-T022: Buffer
           Explicitly allocated slack between Activities or at schedule
           boundaries.
           — Has: buffer_id (UUID), buffer_type (enum: feeding, project,
             resource, time_between, custom), duration (ISO 8601),
             placement ({before_ref (nullable — Activity/Milestone ref),
             after_ref (nullable — Activity/Milestone ref),
             at_boundary (nullable — schedule start/end)}),
             consumption_tracking ({original_duration, remaining_duration,
             consumption_rate (computed)}), schedule_ref (Schedule
             TERM-T010 ref), rationale (text — why this buffer exists),
             created_at, created_by.
           — Buffer types from Critical Chain Project Management (Goldratt):
             feeding buffer = before a critical path merge point, protecting
             the critical chain from feeding chain delays. project buffer
             = at the end of the project, protecting the completion date.
             resource buffer = before a critical resource is needed,
             ensuring the resource is available when needed. time_between
             = between consecutive activities, preventing back-to-back
             scheduling (Property T8: perception asymmetry).
           — Distinguished from TransitionTime (TERM-T029): Buffer is
             deliberate schedule protection — slack intentionally added
             to absorb variation. TransitionTime is an operational
             requirement — time required for changeover/cleanup/travel
             that cannot be compressed below a physical minimum.
           — Buffer consumption tracking: as activities consume their
             buffers (by running longer than planned), the consumption
             rate provides early warning of schedule risk. This is a
             core CCPM metric.
```

### Category D — Bookings & Resources

```
TERM-T004: Booking
           A confirmed allocation of a SchedulableResource to an Activity
           during a specific TimeWindow.
           — Has: booking_id (UUID), organization_id, activity_ref
             (Activity TERM-T007 ref), resource_ref (SchedulableResource
             TERM-T016 ref), timewindow (TimeWindow TERM-T002 ref),
             schedule_ref (Schedule TERM-T010 ref), booking_type (enum:
             confirmed, tentative, held, waitlisted), scheduling_rationale
             (text — why this resource at this time was selected; mandatory
             for auditable scheduling decisions), commercial_agreement_ref
             (nullable — BUSINESS Reservation TERM-023 ref if this booking
             has a commercial counterpart), confirmation_timestamp (UTC),
             hold_expiry (nullable — for held bookings: when the hold
             expires and the slot is released), status (per SM-T002),
             cancellation_reason (nullable), version, created_at,
             created_by.
           — The bridge between Activity (what needs to happen) and
             SchedulableResource (who/what does it) at a specific time
             (when it happens). A Booking is the atomic unit of resource
             commitment.
           — Distinguished from BUSINESS Reservation (TERM-023) per
             Principle P4: Booking = temporal allocation (TEMPORAL).
             Reservation = commercial agreement (BUSINESS). When you book
             a doctor's appointment: TEMPORAL creates a Booking (Dr. Smith,
             Room 3, 2:00-2:30 PM). BUSINESS creates a Reservation
             (patient co-pay, cancellation policy, insurance billing).
             Booking carries commercial_agreement_ref → Reservation.
             Reservation references Booking for temporal fields.
           — scheduling_rationale is mandatory, not optional. Every
             booking must explain why this resource and this time were
             selected. This supports bias auditing (ACT-T007) and
             regulatory compliance.

TERM-T016: SchedulableResource
           An entity with temporal availability that can be assigned to
           Activities via Bookings.
           — Has: resource_id (UUID), organization_id, name, description,
             resource_type (enum: person, equipment, room, vehicle,
             compute, facility, generic), calendar_refs[] (Calendar
             TERM-T001 refs — one or more calendars defining working
             periods), availability_ref (computed — Availability TERM-T003
             ref), capacity_level ({total (integer — concurrent booking
             slots), unit_type (enum: count, percentage, custom)}),
             skills[] ({skill_name, proficiency_level}),
             location (nullable — for co-location constraints),
             preference_declarations[] ({preference_type (enum:
             preferred_times, avoided_times, max_consecutive_hours,
             consecutive_shift_limit, overtime_consent, break_requirements,
             location_preference, activity_type_preference), value,
             priority (enum: hard_constraint, preference),
             legal_basis (nullable — GOVERNANCE ConsentRecord TERM-G027
             ref or Norm TERM-G001 ref for legally-backed preferences)}),
             physical_asset_ref (nullable — PHYSICAL PhysicalAsset
             TERM-P003 ref; state maps to Availability per INT-T003),
             cost_rate (nullable — for optimization: BUSINESS-owned cost
             per time unit, referenced not duplicated),
             status (enum: active, inactive, on_leave, decommissioned),
             metadata{}, tags[], created_at, created_by.
           — Anything that can be scheduled is a SchedulableResource:
             people, equipment, rooms, vehicles, compute capacity.
             The common properties are Calendar (when available), capacity
             (how many concurrent assignments), and skills/capabilities
             (what it can do).
           — capacity_level enables partial availability: a degraded
             machine at 50% throughput, a part-time employee at 0.5 FTE,
             a conference room with reduced capacity for social distancing.
           — preference_declarations: legal backing is critical.
             "I prefer mornings" is a preference. "I cannot work more than
             48 hours per week" is a hard_constraint with legal_basis
             referencing EU Working Time Directive. Both are expressed in
             the same structure with different priority levels.
           — Cross-substrate: physical_asset_ref links to PHYSICAL
             PhysicalAsset. State mapping (INT-T003): PHYSICAL Operational
             → TEMPORAL Available. Degraded → Conditionally Available
             (reduced capacity_level). LockedOut → Unavailable. Shutdown/
             Decommissioned → Unavailable (permanent). This is the
             PHYSICAL→TEMPORAL availability feed.

TERM-T017: ResourceRequirement
           A declarative specification of what resources an Activity needs.
           — Has: requirement_id (UUID), activity_ref (Activity TERM-T007
             ref), quantity (integer — how many resources needed),
             resource_type (enum matching SchedulableResource types),
             required_skills[] ({skill_name, minimum_proficiency}),
             duration_override (nullable — if resource needed for less
             than full activity duration), synchronization_mode (enum:
             all_simultaneous, sequential, any_subset),
             co_location_required (boolean — all resources must be at
             same location), temporal_alignment (enum: exact_overlap,
             partial_overlap, adjacent), substitution_rules[]
             (nullable — alternative resource specs if primary unavailable),
             priority (integer — for resource assignment ordering),
             created_at, created_by.
           — Declarative: says WHAT is needed, not WHO specifically. "2
             nurses with ICU certification" not "Nurse Jones and Nurse
             Smith." Specific assignment is the solver's job.
           — synchronization_mode: all_simultaneous = all required
             resources must be available during the same TimeWindow
             (surgery: surgeon + anesthesiologist + OR + equipment).
             sequential = resources needed one after another (patient
             sees doctor, then lab, then pharmacy). any_subset = any N
             of M possible resources suffice (any 2 of 5 available
             conference rooms).
           — Multi-resource synchronization — finding TimeWindows where
             ALL required resources are simultaneously available — is
             the computationally hardest scheduling operation and MUST
             be explicitly supported (CAP-T013). This is the operation
             that makes scheduling NP-hard in practice.
```

### Category E — Workforce Patterns

```
TERM-T018: Shift
           A named recurring working time pattern with labor constraint
           metadata.
           — Has: shift_id (UUID), organization_id, name, description,
             shift_type (enum: day, evening, night, split, rotating,
             on_call, custom), start_time (local time), end_time (local
             time), duration (computed), break_rules[] ({break_type
             (enum: meal, rest, short), duration, earliest_start_offset,
             latest_start_offset, paid (boolean)}), recurrence_ref
             (Recurrence TERM-T005 ref — when this shift repeats),
             rotation_ref (nullable — Rotation TERM-T019 ref if part
             of a rotation), eligibility_rules[] ({resource_type,
             required_skills[], minimum_rest_before (duration),
             maximum_consecutive_shifts (integer), overtime_threshold
             (duration)}), resource_requirements[]
             (ResourceRequirement TERM-T017 refs — how many resources
             needed per shift), labor_constraints[] ({constraint_type,
             legal_basis (GOVERNANCE Norm ref), parameters{}}),
             premium_multiplier (nullable — referenced from BUSINESS
             for pay calculation), status (enum: active, inactive),
             created_at, created_by.
           — Distinct from Recurrence (TERM-T005): Recurrence is a
             temporal mechanism (when things repeat). Shift is a domain
             concept composing Recurrence + ResourceRequirement + labor
             constraint metadata. A Shift is "the night shift: 11 PM to
             7 AM, with a 30-minute meal break, requiring 3 nurses with
             ICU certification, subject to 11-hour minimum rest and
             48-hour weekly maximum."
           — labor_constraints carry legal_basis references to GOVERNANCE
             Norms. These are not optional preferences — they are legally
             binding scheduling constraints consumed from GOVERNANCE per
             INT-T004.

TERM-T019: Rotation
           A cyclical assignment distributing Activities or Shifts across
           a SchedulableResource pool over a repeating period.
           — Has: rotation_id (UUID), organization_id, name, description,
             rotation_type (enum: fixed_cycle, balanced_load,
             preference_weighted, seniority_based, custom),
             resource_pool[] (SchedulableResource TERM-T016 refs),
             shift_pattern[] (ordered Shift TERM-T018 refs defining the
             rotation cycle), cycle_length (duration — how long before
             the pattern repeats), fairness_metrics ({distribution_equity
             (computed — standard deviation of assignments per resource),
             weekend_equity (computed — distribution of weekend shifts),
             holiday_equity (computed — distribution of holiday shifts),
             preference_satisfaction (computed — percentage of preference
             declarations honored)}), rebalance_trigger ({threshold
             (numeric — equity deviation that triggers rebalancing),
             frequency (duration — minimum time between rebalances)}),
             status (enum: active, paused, completed), created_at,
             created_by.
           — Drives Property T9 (Fairness). Rotation exists because
             equitable distribution of scheduling burden is a legal
             requirement (ASM-T010), not an optimization preference.
             "Everyone takes their fair share of night shifts" is
             enforceable by labor arbitrators.
           — fairness_metrics are first-class computed properties, not
             optional analytics. An Auditor (ACT-T007) can query these
             metrics to detect systematic bias. If distribution_equity
             exceeds threshold, rebalancing is triggered.

TERM-T023: Cadence
           An organizational-level recurring temporal structure that
           governs planning, review, and reporting cycles.
           — Has: cadence_id (UUID), organization_id, name, description,
             purpose (enum: planning, review, reporting, fiscal,
             operational, ceremonial, custom), recurrence_ref (Recurrence
             TERM-T005 ref — the temporal engine), cycle_length (duration),
             boundary_rules[] ({boundary_type (enum: cycle_start,
             cycle_end, mid_cycle), action (text — what happens at this
             boundary: sprint review, quarter close, annual planning),
             mandatory (boolean)}), phase_within_cadence[]
             ({phase_name, start_offset (duration from cycle start),
             duration, activities[] (Activity TERM-T007 refs)}),
             alignment_rules[] (nullable — how this Cadence aligns with
             other Cadences: fiscal quarters align with sprint boundaries),
             status (enum: active, paused, archived), created_at,
             created_by.
           — Distinct from Recurrence (TERM-T005): Cadence is the
             organizational wrapper; Recurrence is the temporal engine
             inside it. A two-week sprint Cadence USES a Recurrence
             (FREQ=WEEKLY;INTERVAL=2) but ADDS: sprint planning on day 1,
             daily standups, sprint review on day 10, retrospective on
             day 10. The Recurrence doesn't know about sprints; the
             Cadence defines the organizational meaning.
           — Cadences create temporal structure for organizations:
             fiscal quarters for reporting, sprints for development,
             academic terms for education, maintenance cycles for
             equipment, shift rotations for workforce. They are the
             temporal scaffolding of organizational life.
```

### Category F — Conflicts & Disruptions

```
TERM-T014: Conflict
           A detected state where Bookings or Activities require the same
           resource during overlapping TimeWindows, or where Constraints
           are mutually unsatisfiable.
           — Has: conflict_id (UUID), conflict_type (enum: double_booking,
             resource_overload, constraint_violation, dependency_cycle,
             capacity_exceeded, policy_violation),
             conflicting_entities[] ({entity_type, entity_ref} — the
             Bookings, Activities, or Constraints in conflict),
             resource_ref (nullable — SchedulableResource at the center
             of the conflict, if resource-based), timewindow (nullable —
             the overlapping period), severity (enum: critical, major,
             minor, informational), detected_at (UTC timestamp),
             detected_by (agent_id — human or AI), resolution_ref
             (nullable — Resolution TERM-T015 ref once resolved),
             status (per SM-T004), created_at.
           — Conflict detection is proactive and continuous. The system
             MUST detect Conflicts as they arise — not wait for a
             downstream failure. Double-booking (two Bookings for the
             same single-capacity resource at overlapping times) is the
             most common type.
           — severity: critical = schedule cannot proceed without
             resolution (dependency cycle, hard constraint violation).
             major = significant impact (double-booking, capacity
             exceeded). minor = suboptimal but workable (soft constraint
             violation). informational = detected but no action required
             (preference not honored).

TERM-T015: Resolution
           A decision record documenting how a Conflict was resolved.
           — Has: resolution_id (UUID), conflict_ref (Conflict TERM-T014
             ref), resolution_type (enum: reschedule, reassign, split,
             defer, override, cancel, escalate, accept_conflict),
             authority (agent_id — who authorized this resolution),
             justification (text — why this resolution was chosen),
             affected_bookings[] (Booking TERM-T004 refs modified by
             this resolution), affected_activities[] (Activity TERM-T007
             refs modified), affected_parties_notified (boolean — were
             all affected participants notified), notification_refs[]
             (COMMUNICATION message refs for notifications sent),
             reversible (boolean), reversal_deadline (nullable — by
             when the resolution can be reversed), constraint_relaxed_ref
             (nullable — Constraint TERM-T006 ref if resolution involved
             constraint relaxation), status (enum: proposed, approved,
             applied, reversed), created_at, created_by.
           — Resolution lifecycle: proposed (AI or human proposes) →
             approved (authority approves, required for hard constraint
             relaxation) → applied (changes enacted) → optionally
             reversed (if reversible and within reversal_deadline).
           — resolution_type: reschedule = move activity to different
             time. reassign = assign different resource. split = break
             activity into smaller pieces. defer = postpone indefinitely.
             override = proceed despite conflict (with justification).
             cancel = remove the conflicting activity. escalate = pass
             to higher authority. accept_conflict = acknowledge conflict
             exists and proceed anyway (e.g., intentional overbooking).
           — Parallels GOVERNANCE enforcement lifecycle depth: every
             conflict resolution is a record with authority, justification,
             and affected parties — not an ad-hoc modification.

TERM-T013: Disruption
           An event that invalidates part of an existing Schedule, requiring
           assessment and potential rescheduling.
           — Has: disruption_id (UUID), disruption_type (enum:
             resource_unavailable, activity_delayed, priority_changed,
             new_constraint_added, constraint_removed, demand_changed,
             external_event, equipment_failure, no_show, custom),
             source (structured — what triggered the disruption:
             cross-substrate event ref, human report, system detection),
             affected_schedule_ref (Schedule TERM-T010 ref),
             affected_activities[] (Activity TERM-T007 refs directly
             affected), cascade_analysis ({cascade_depth (integer —
             how many downstream activities affected), cascade_breadth
             (integer — how many parallel schedules affected),
             affected_resources[] (SchedulableResource refs),
             estimated_recovery_time (duration)}),
             rescheduling_recommendation (nullable — proposed Resolution
             or set of Resolutions), severity (enum: critical, major,
             minor), response_deadline (nullable — by when the disruption
             must be addressed), status (per SM-T005), created_at.
           — Disruption is the normal operating state (ASM-T003, Property
             T3). 73% of schedules are disrupted. The substrate treats
             disruption handling as the primary operation.
           — cascade_analysis is a first-class computed property. When a
             resource becomes unavailable, the system computes the full
             propagation: all activities using that resource, all
             activities dependent on those activities, all schedules
             containing those activities, all resources involved in
             alternative assignments. Property T7: cascades propagate
             laterally across ALL schedules sharing a resource.
           — Cross-substrate triggers: PHYSICAL emits
             `substrate.physical.asset.degraded` → TEMPORAL creates
             Disruption (resource_unavailable). COMMUNICATION participant
             declines → Disruption (resource_unavailable). BUSINESS
             priority changes → Disruption (priority_changed). GOVERNANCE
             new compliance constraint → Disruption (new_constraint_added).
```

### Category G — Capacity & Queuing

```
TERM-T028: Capacity
           Aggregate resource availability over a time horizon for
           demand-vs-capacity planning.
           — Has: capacity_id (UUID), organization_id, resource_pool_ref
             (SchedulableResource[] TERM-T016 refs — the pool being
             measured), horizon_ref (Horizon TERM-T012 ref),
             time_buckets[] ({period_start, period_end, total_units,
             committed_units, available_units, utilization_rate
             (computed)}), unit_type (enum: hours, FTE, units,
             throughput, custom), demand_forecast_ref (nullable —
             KNOWLEDGE Proposition TERM-K001 ref for demand predictions),
             supply_constraints[] (nullable — factors limiting capacity:
             budget, headcount cap, equipment maintenance),
             gap_analysis ({periods_with_deficit[], deficit_magnitude,
             recommended_action (enum: hire, rent, reschedule, defer)}),
             snapshot_timestamp (UTC), created_at, created_by.
           — The pattern beneath CRP in MRP II, healthcare capacity
             planning, workforce capacity management, and infrastructure
             capacity modeling. "Can we deliver by Q3?" is a Capacity
             question: total available hours minus committed hours in the
             horizon equals remaining capacity for new work.
           — gap_analysis identifies periods where demand exceeds supply
             and recommends action. TEMPORAL identifies the gap; BUSINESS
             handles procurement (NG-T007). Capacity.gap_analysis
             references are consumed by BUSINESS for hiring/purchasing
             decisions.
           — Cross-substrate: demand_forecast_ref links to KNOWLEDGE
             for probabilistic demand predictions. BUSINESS provides
             demand signals (orders, bookings, seasonal patterns).
             TEMPORAL computes capacity against demand.

TERM-T029: TransitionTime
           Time required to prepare a resource for the next activity after
           completing the current one.
           — Has: transition_id (UUID), from_activity_type (Activity type
             or specific activity_ref), to_activity_type (Activity type
             or specific activity_ref), resource_ref (SchedulableResource
             TERM-T016 ref), minimum_duration (ISO 8601 — physical minimum
             that cannot be compressed), typical_duration (ISO 8601 —
             normal operational duration), includes[] (enum: cleanup,
             changeover, setup, travel, rest, inspection, calibration),
             sequence_dependent (boolean — does transition time depend
             on the specific from/to pair?), travel_details (nullable —
             for travel-type transitions: {location_from, location_to,
             travel_mode (enum: walking, driving, transit, flight),
             travel_duration_model (enum: fixed, distance_based,
             traffic_aware)}), created_at, created_by.
           — Fundamental to: manufacturing (setup/changeover time between
             different product runs), healthcare (OR turnover between
             surgeries), transportation (deadheading — moving an empty
             vehicle to the next pickup), maintenance (cleanup after
             repair), and general scheduling (travel time between
             locations).
           — sequence_dependent: in manufacturing, changing from Product A
             to Product B may take 30 minutes, but changing from Product A
             to Product C may take 2 hours (different tooling). Sequence-
             dependent TransitionTimes are a major scheduling complexity
             factor.
           — Distinguished from Buffer (TERM-T022): TransitionTime is an
             operational requirement — the OR cannot be used until it is
             cleaned and sterilized. Buffer is deliberate slack — extra
             time added as schedule protection. TransitionTime has a
             physical minimum_duration; Buffer duration is a planning
             decision.

TERM-T030: Waitlist
           An ordered queue of requestors awaiting future scheduling
           openings.
           — Has: waitlist_id (UUID), organization_id, name,
             resource_or_service_ref (what is being waited for:
             SchedulableResource TERM-T016 ref or Activity type),
             entries[] ({entry_id, requestor (agent_id or external
             identifier), requested_preferences ({time_preferences[],
             resource_preferences[], duration}), priority (integer),
             position (computed — based on priority and enrollment
             order), enrollment_timestamp (UTC), expiration_policy
             ({type (enum: fixed_date, duration_from_enrollment,
             never), value}), callback_trigger (enum:
             slot_available, daily_digest, manual_check),
             status (enum: active, offered, accepted, expired,
             withdrawn)}), ordering_policy (enum: fifo,
             priority_then_fifo, clinical_urgency, custom),
             notification_policy ({channel, lead_time}),
             max_size (nullable — maximum entries allowed),
             created_at, created_by.
           — The pattern beneath healthcare waitlists (Epic Cadence wait
             lists), restaurant reservation waitlists, course enrollment
             waitlists, airline standby lists, and organ transplant
             priority queues.
           — Distinguished from Conflict (TERM-T014): a Conflict is a
             detected problem requiring resolution. A Waitlist is a
             managed queue for future scheduling — no conflict exists
             because no Booking has been made.
           — Distinguished from Booking (TERM-T004): a Booking is a
             confirmed allocation. A Waitlist entry is a request for
             future allocation. When a slot opens, the next Waitlist
             entry is offered the slot; if accepted, it becomes a Booking.
           — ordering_policy: fifo = first-come, first-served (restaurant).
             priority_then_fifo = priority ordering with FIFO tiebreaker
             (healthcare urgency). clinical_urgency = medical triage
             ordering. Custom allows domain-specific ordering rules.
```

### Category H — Optimization, Policy & AI Authority

```
TERM-T024: SchedulingObjective
           An explicit optimization goal for scheduling decisions.
           — Has: objective_id (UUID), organization_id, name, description,
             metric (enum: makespan, throughput, utilization, wait_time,
             tardiness, fairness, cost, preference_satisfaction,
             resource_balance, custom), direction (enum: minimize,
             maximize), weight (numeric — relative importance when
             multiple objectives are combined), measurement_method
             (structured — how the metric is computed from Schedule data),
             target_value (nullable — desired metric value),
             acceptable_range ({min, max} — range within which the
             metric is considered satisfactory), created_at, created_by.
           — Analogous to DESIGN's DesignSpace objectives[]. Multiple
             SchedulingObjectives define multi-objective optimization.
             A hospital may simultaneously minimize patient wait time
             (weight 0.4), maximize OR utilization (weight 0.3), and
             maximize scheduling fairness for surgeons (weight 0.3).
           — Schedule.quality_scores[] maps each SchedulingObjective
             to its achieved score. This makes optimization tradeoffs
             explicit and auditable: "We achieved 85% OR utilization
             but only P50 patient wait time — do we adjust weights?"
           — Property T2 motivation: scheduling is NP-hard. The
             substrate must make tradeoffs explicit rather than hiding
             them inside solver implementations. SchedulingObjective
             is how tradeoffs are declared; quality_scores is how
             outcomes are measured.

TERM-T021: TemporalServiceMetric
           A temporal performance measurement against service level targets.
           — Has: metric_id (UUID), organization_id, name, description,
             metric_type (enum: response_time, wait_time, throughput,
             on_time_delivery, booking_confirmation_latency, schedule_
             adherence, custom), target_duration (ISO 8601 duration),
             threshold_percentiles ({P50 (duration), P95 (duration),
             P99 (duration)}), measurement_window (duration — over what
             period the metric is computed), current_performance
             ({P50_actual, P95_actual, P99_actual, sample_count}),
             breach_detected (boolean), breach_timestamp (nullable),
             breach_count_in_window (integer), trend ({direction (enum:
             improving, stable, degrading), rate}),
             obligation_ref (nullable — GOVERNANCE Obligation TERM-G005
             ref if this metric is tied to an SLA), created_at,
             created_by.
           — NOTE: Renamed from "SLA" to TemporalServiceMetric.
             Contractual and penalty aspects are GOVERNANCE-owned.
             TemporalServiceMetric is the clock — it measures temporal
             performance. GOVERNANCE Obligation (TERM-G005) is the
             contract — its action_required references
             TemporalServiceMetric. GOVERNANCE Sanction is the penalty.
             TEMPORAL emits `substrate.temporal.service_metric.breached`;
             GOVERNANCE processes through Obligation → Violation →
             Sanction lifecycle.
           — Cross-substrate: the cleanest example of P3 (Define vs
             Enforce). TEMPORAL defines the measurement. GOVERNANCE
             defines the consequence. Neither duplicates the other.

TERM-T026: SchedulingPolicy
           A declarative rule constraining or guiding scheduling decisions.
           — Has: policy_id (UUID), organization_id, name, description,
             policy_type (enum: priority, fairness, efficiency, compliance,
             preference, overbooking, preemption, batching, disruption_
             response, custom),
             parameters ({
               — priority: {priority_rules[] ({condition, priority_value})}
               — fairness: {equity_metric (enum: distribution_equality,
                 preference_satisfaction, workload_balance), threshold,
                 rebalance_frequency}
               — efficiency: {target_metric (enum: utilization, idle_time,
                 throughput), target_value}
               — compliance: {governance_norm_ref (GOVERNANCE Norm
                 TERM-G001 ref), temporal_constraint_spec (structured:
                 {constraint_type, duration, window, scope})}
               — preference: {preference_weight (0.0-1.0), override_
                 conditions[]}
               — overbooking: {overbooking_rate (percentage),
                 no_show_probability_model (enum: historical_average,
                 day_of_week, seasonal, ml_model), max_overflow (integer
                 — maximum excess bookings allowed)}
               — preemption: {preemption_allowed (boolean),
                 priority_threshold (integer — minimum priority
                 difference for preemption), preempted_activity_handling
                 (enum: reschedule, defer, cancel, waitlist)}
               — batching: {batch_criterion (enum: activity_type,
                 resource_type, location, time_proximity),
                 min_batch_size, max_batch_size, batch_window (duration)}
               — disruption_response: {response_threshold (enum:
                 immediate, within_hour, next_cycle, manual),
                 auto_reschedule (boolean), cascade_limit (integer)}
             }),
             scope (structured — where this policy applies: organization,
             department, resource_pool, schedule_type),
             effective_from (UTC timestamp), effective_until (nullable),
             legal_basis (nullable — GOVERNANCE Norm ref for legally-
             mandated policies), status (enum: active, suspended,
             archived), created_at, created_by.
           — SchedulingPolicy is the mechanism by which organizational
             rules, legal requirements, and operational preferences are
             injected into the scheduling process. The solver consumes
             SchedulingPolicies as additional constraints and objective
             modifiers.
           — compliance-type policies consume GOVERNANCE Norms with
             structured temporal_constraint_spec. Example: EU Working Time
             Directive → GOVERNANCE Norm → SchedulingPolicy (compliance)
             with temporal_constraint_spec: {constraint_type:
             "maximum_weekly_hours", duration: "PT48H", window: "P7D",
             scope: "per_worker"}. TEMPORAL enforces proactively during
             schedule creation; GOVERNANCE enforces retroactively via
             ComplianceAssessment.
           — overbooking-type resolves OQ-T004: overbooking is a policy,
             not a primitive. Airlines (4-8%), hotels (5-15%), and
             healthcare (varies) use overbooking to compensate for no-
             shows. The policy specifies the rate, the probability model,
             and the overflow limit.

TERM-T025: TemporalEnvelope
           Bounded AI agent authority over scheduling operations.
           — Has: envelope_id (UUID), organization_id, agent_id,
             max_scheduling_horizon (duration — how far into the future
             the agent may schedule), max_bookings_per_period ({period
             (duration), limit (integer)}), accessible_resource_pools[]
             (SchedulableResource pool refs the agent may schedule),
             conflict_resolution_authority (enum: propose_only,
             resolve_minor, resolve_major, resolve_all),
             constraint_relaxation_authority (enum: none,
             soft_constraints_only, with_justification),
             override_limits ({max_overrides_per_period (integer),
             override_types_allowed[] (Resolution types)}),
             schedule_types_allowed[] (Schedule types the agent may
             create/modify), prohibited_operations[] (operations the
             agent may never perform regardless of other settings),
             parent_envelope_ref (nullable — higher-authority envelope
             from which this is derived), effective_from, effective_until
             (nullable), created_at, created_by.
           — Sits in the Agent authority chain: Business Agent Envelope →
             GovernanceEnvelope → Epistemic Envelope → **TemporalEnvelope**
             → DesignEnvelope → Compute Envelope → Communicative Envelope
             → PhysicalEnvelope. An agent must have epistemic authority
             (may reason about this domain) before temporal authority
             (may schedule resources in this domain). Temporal authority
             is a resource-allocation step between reasoning permission
             and physical resource commitment.
           — conflict_resolution_authority: propose_only = agent proposes
             resolutions but human must approve. resolve_minor = agent
             may resolve minor conflicts autonomously. resolve_major =
             agent may resolve major conflicts. resolve_all = agent may
             resolve all conflicts (highest authority, typically reserved
             for ACT-T004 General Temporal AI).
           — constraint_relaxation_authority: none = agent may not relax
             any constraints. soft_constraints_only = agent may relax
             soft constraints but not hard. with_justification = agent
             may relax soft constraints and propose hard constraint
             relaxation with justification (human must approve hard
             relaxation).
           — Does NOT constrain viewing one's own schedule. Read access
             is ACL-based per Section 9, not envelope-based.
```

---

## 4. CORE CAPABILITIES (WHAT THE SYSTEM MUST DO)

> Capabilities use RFC 2119 language: MUST (required), SHOULD
> (recommended), MAY (optional). Each capability references the
> primitives it operates on and the actors who invoke it.

### Calendar & Time Management

```
CAP-T001: The system MUST support creation and management of Calendars
          (TERM-T001). A Calendar defines working periods, exceptions,
          and scheduling context within a scope. The system MUST support
          hierarchical Calendar inheritance (organization → department →
          team → individual) with exception override at each level.
          When a parent Calendar's working periods change, all child
          Calendars MUST be re-evaluated for consistency.
          Actors: ACT-T002.

CAP-T002: The system MUST support creation, intersection, and comparison
          of TimeWindows (TERM-T002). TimeWindow arithmetic MUST include:
          intersection (overlapping period), union (combined period),
          difference (gaps between windows), and containment testing
          (is window A within window B). All operations MUST handle
          timezone conversions correctly via CalendarSystem (TERM-T027).
          Actors: ACT-T001, ACT-T003, ACT-T004.

CAP-T003: The system MUST compute Availability (TERM-T003) for any
          SchedulableResource over any Horizon. Availability computation
          MUST account for: Calendar working periods, existing Bookings
          (subtract committed time), Constraints (apply temporal
          restrictions), capacity levels (partial availability for
          multi-capacity resources), and TransitionTimes (TERM-T029)
          between consecutive activities. Availability MUST support
          visibility levels (full_detail, busy_free, slots_only) per
          TRUST-T001 and TRUST-T004.
          Actors: ACT-T001, ACT-T003, ACT-T004, ACT-T005, ACT-T008.

CAP-T004: The system MUST support Recurrence (TERM-T005) creation and
          instance generation with full RFC 5545 RRULE semantics plus
          extensions for rotating shifts, academic terms, and fiscal
          periods. The system MUST correctly handle: EXDATE (exception
          dates), EXRULE (exception rules), timezone transitions within
          recurrence patterns (a weekly meeting at "3 PM local" shifts
          UTC offset at DST transitions), and unbounded recurrences
          (no COUNT or UNTIL). Instance generation MUST be lazy (generate
          on demand, not pre-materialized).
          Actors: ACT-T001, ACT-T002, ACT-T003.

CAP-T005: The system MUST support CalendarSystem (TERM-T027) registration
          and temporal interpretation. All date/time storage MUST be UTC.
          The system MUST correctly convert between UTC and any registered
          CalendarSystem for display and input. The system MUST handle:
          DST transitions (including the ambiguous hour when clocks fall
          back), leap seconds (for precision scheduling contexts), and
          non-Gregorian calendar systems (Islamic, Hebrew, Chinese lunar,
          Japanese Imperial). The system SHOULD support RFC 7529
          (non-Gregorian recurrence rules in iCalendar).
          Actors: ACT-T002.
```

### Activity & Dependency Management

```
CAP-T006: The system MUST support creation and lifecycle management of
          Activities (TERM-T007). Activities follow SM-T001
          (draft → scheduled → in_progress → completed | cancelled |
          deferred). The system MUST support all duration types (fixed,
          estimated with PERT three-point, range). When an Activity's
          actual duration deviates from estimated by more than a
          configurable threshold, the system MUST emit an event for
          downstream analysis.
          Actors: ACT-T001, ACT-T003, ACT-T004.

CAP-T007: The system MUST support Dependency (TERM-T009) creation and
          validation between Activities. The system MUST support all
          four dependency types (FS, SS, FF, SF) with optional lag/lead.
          The system MUST detect dependency cycles and report them as
          Conflicts (TERM-T014, dependency_cycle type). The system MUST
          compute critical path and slack from the dependency network
          within a Timeline (TERM-T011).
          Actors: ACT-T001, ACT-T003, ACT-T004.

CAP-T008: The system MUST support Constraint (TERM-T006) creation and
          evaluation with hardness levels (hard, soft, preference). The
          system MUST support constraint relaxation: when no feasible
          Schedule exists, soft and preference Constraints MUST be
          relaxable in relaxation_priority order. Each relaxation MUST
          create a Resolution (TERM-T015) record. Hard Constraints MUST
          NOT be automatically relaxed — infeasibility with only hard
          Constraints MUST be reported to human authority.
          Actors: ACT-T001, ACT-T002, ACT-T003, ACT-T004.

CAP-T009: The system MUST support Deadline (TERM-T020) creation, tracking,
          and escalation. The system MUST evaluate notification_triggers
          and fire notifications at specified offsets before the due date.
          The system MUST evaluate escalation_rules when a Deadline is
          breached. Deadline status MUST transition automatically:
          pending → approaching (when first notification_trigger fires)
          → met (when target activity completes before due) or breached
          (when due passes without completion).
          Actors: ACT-T001, ACT-T003, ACT-T004.
```

### Schedule Creation & Optimization

```
CAP-T010: The system MUST support Schedule (TERM-T010) creation by
          assembling Activities, Dependencies, Constraints, and
          ResourceRequirements into a constraint-satisfaction problem
          and invoking a solver via COMPUTE Pipeline (INT-T002). The
          system MUST accept the SchedulingSolution, validate it against
          all hard Constraints, and produce a feasible Schedule with
          Bookings. If the solver returns infeasible, the system MUST
          report which Constraints are unsatisfiable.
          Actors: ACT-T001, ACT-T003, ACT-T004.

CAP-T011: The system MUST support Schedule feasibility assessment. Given
          a set of Activities, Dependencies, Constraints, and available
          Resources, the system MUST determine whether a feasible
          Schedule exists without necessarily producing one. The system
          SHOULD report: feasibility (yes/no/conditional), estimated
          completion date range, and bottleneck resources.
          Actors: ACT-T001, ACT-T003, ACT-T004.

CAP-T012: The system MUST create immutable Timeline (TERM-T011) snapshots
          whenever a Schedule is modified. The system MUST compute
          critical path and per-activity slack for each Timeline. The
          system MUST support delta computation between any two Timelines
          of the same Schedule (activities added/removed/moved, resources
          changed, constraints relaxed/restored). Timelines MUST be
          integrity-hashed for tamper evidence.
          Actors: ACT-T001, ACT-T003, ACT-T004, ACT-T007.

CAP-T013: The system MUST support multi-objective schedule optimization
          via SchedulingObjectives (TERM-T024). When multiple objectives
          are specified, the system MUST report quality_scores for each
          objective in the produced Schedule. The system SHOULD support
          Pareto frontier exploration: presenting alternative Schedules
          that trade off between objectives. The system MUST NOT silently
          favor one objective over another — all tradeoffs must be
          explicit in quality_scores.
          Actors: ACT-T001, ACT-T002, ACT-T004.

CAP-T014: The system MUST support Horizon (TERM-T012) configuration
          with type-appropriate resolution. The system MUST enforce
          resolution boundaries: activities MUST NOT be scheduled at
          finer granularity than the Horizon's resolution allows. The
          system SHOULD support rolling Horizons that advance
          automatically with time, triggering re-optimization of the
          exposed scheduling window.
          Actors: ACT-T002.

CAP-T015: The system MUST support Buffer (TERM-T022) creation with
          consumption tracking. The system MUST track buffer consumption
          as activities consume planned slack. The system SHOULD alert
          when buffer consumption rate exceeds a configurable threshold
          (CCPM fever chart). Buffer placement MUST be validated against
          the dependency network (feeding buffers at merge points,
          project buffers at schedule end).
          Actors: ACT-T001, ACT-T003, ACT-T004.
```

### Booking & Resource Management

```
CAP-T016: The system MUST support Booking (TERM-T004) creation with
          mandatory scheduling_rationale. The system MUST verify resource
          Availability before confirming a Booking. The system MUST
          detect and report Conflicts (TERM-T014) when a Booking would
          create a double-booking or exceed resource capacity. Tentative
          and held Bookings MUST expire per their hold_expiry.
          Actors: ACT-T001, ACT-T003, ACT-T004, ACT-T008.

CAP-T017: The system MUST support SchedulableResource (TERM-T016)
          registration with Calendar assignment, capacity configuration,
          skill declaration, and preference declarations. The system MUST
          distinguish between hard_constraint preferences (legally backed)
          and preference-level preferences (best-effort). When a resource's
          status changes (active → on_leave, etc.), the system MUST
          create Disruptions for all affected Bookings.
          Actors: ACT-T002, ACT-T005.

CAP-T018: The system MUST support ResourceRequirement (TERM-T017)
          evaluation including multi-resource synchronization. For
          all_simultaneous mode, the system MUST find TimeWindows where
          ALL required resources are simultaneously available. For
          sequential mode, the system MUST find consecutive TimeWindows
          for each resource. For any_subset mode, the system MUST find
          any qualifying subset of resources. co_location_required MUST
          be enforced when set.
          Actors: ACT-T001, ACT-T003, ACT-T004.

CAP-T019: The system MUST support TransitionTime (TERM-T029) enforcement
          between consecutive Activities on the same resource. When
          computing Availability and creating Bookings, TransitionTimes
          MUST be subtracted from available capacity. Sequence-dependent
          TransitionTimes MUST be evaluated based on the specific
          from/to activity pair.
          Actors: ACT-T001, ACT-T003, ACT-T004.
```

### Workforce & Shift Management

```
CAP-T020: The system MUST support Shift (TERM-T018) definition with
          break rules, eligibility requirements, and labor constraint
          enforcement. The system MUST validate that Shift assignments
          respect: minimum rest periods between shifts, maximum
          consecutive shift limits, weekly hour maximums, and all
          labor_constraints with legal_basis references.
          Actors: ACT-T001, ACT-T002, ACT-T003.

CAP-T021: The system MUST support Rotation (TERM-T019) creation and
          fairness metric computation. The system MUST compute
          distribution_equity, weekend_equity, holiday_equity, and
          preference_satisfaction for each Rotation. When fairness
          metrics exceed the configured threshold, the system MUST
          trigger rebalancing. Fairness metrics MUST be available to
          Auditors (ACT-T007) for bias detection.
          Actors: ACT-T001, ACT-T002, ACT-T003, ACT-T007.

CAP-T022: The system MUST support Cadence (TERM-T023) definition with
          boundary rules and phase structures. The system MUST generate
          Activities for boundary actions (sprint reviews, quarter closes)
          at appropriate cadence boundaries. The system SHOULD support
          Cadence alignment: verifying that nested Cadences (sprints
          within quarters) have consistent boundaries.
          Actors: ACT-T002.
```

### Conflict Detection & Resolution

```
CAP-T023: The system MUST detect Conflicts (TERM-T014) proactively and
          continuously. Double-booking MUST be detected at Booking
          creation time. Constraint violations MUST be detected at
          Schedule creation and modification time. Dependency cycles
          MUST be detected at Dependency creation time. The system MUST
          NOT allow silent Conflict creation — every detected Conflict
          MUST be recorded and surfaced.
          Actors: ACT-T001, ACT-T003, ACT-T004.

CAP-T024: The system MUST support Resolution (TERM-T015) creation with
          mandatory authority and justification for all resolution types.
          For hard constraint relaxation, Resolution MUST be approved
          by human authority (ACT-T001 or ACT-T002). AI agents (ACT-T003,
          ACT-T004) MAY propose Resolutions and MAY apply Resolutions
          for minor/major Conflicts per their TemporalEnvelope
          conflict_resolution_authority. The system MUST notify all
          affected parties when a Resolution is applied.
          Actors: ACT-T001, ACT-T003, ACT-T004.

CAP-T025: The system SHOULD support automated conflict resolution
          recommendations. Given a Conflict, the system SHOULD evaluate
          feasible Resolution options (reschedule, reassign, split,
          defer) and rank them by impact on Schedule quality_scores.
          Recommendations MUST include scheduling_rationale. Automated
          resolution within TemporalEnvelope authority MAY be applied
          without human approval for minor Conflicts.
          Actors: ACT-T003, ACT-T004.
```

### Disruption & Recovery

```
CAP-T026: The system MUST support Disruption (TERM-T013) creation from
          both internal events (Booking cancellation, Activity delay) and
          cross-substrate events (PHYSICAL asset degradation, GOVERNANCE
          new constraint, COMMUNICATION participant decline). The system
          MUST compute cascade_analysis for each Disruption: identifying
          all directly and transitively affected Activities, Resources,
          and Schedules.
          Actors: ACT-T001, ACT-T003, ACT-T004, ACT-T006.

CAP-T027: The system MUST support disruption-triggered rescheduling.
          When a Disruption affects a Schedule, the system MUST:
          (1) identify affected Activities, (2) evaluate constraint
          feasibility after the disruption, (3) propose rescheduling
          options as Resolution candidates, (4) apply approved
          Resolutions, (5) create a new Timeline snapshot capturing
          the post-disruption state. The response speed MUST be
          configurable per SchedulingPolicy disruption_response type.
          Actors: ACT-T001, ACT-T003, ACT-T004.

CAP-T028: The system MUST track Disruption frequency and patterns per
          resource, schedule type, and time period. The system SHOULD
          emit disruption pattern data as events consumable by KNOWLEDGE
          for historical analysis. The system SHOULD support disruption
          prediction: identifying resources or schedule segments at high
          risk of disruption based on historical patterns.
          Actors: ACT-T003, ACT-T004, ACT-T007.
```

### Capacity & Queuing

```
CAP-T029: The system MUST support Capacity (TERM-T028) computation for
          resource pools over configurable Horizons. The system MUST
          compute: total available capacity, committed capacity, and
          remaining available capacity per time bucket. The system MUST
          perform gap analysis: identifying periods where committed or
          forecasted demand exceeds available supply, and recommending
          action (hire, rent, reschedule, defer). BUSINESS consumes
          gap_analysis for procurement decisions (NG-T007).
          Actors: ACT-T001, ACT-T002, ACT-T004.

CAP-T030: The system MUST support Waitlist (TERM-T030) management with
          configurable ordering policies (FIFO, priority, clinical
          urgency, custom). When a scheduling slot opens (Booking
          cancelled, new Availability), the system MUST offer the slot
          to the next eligible Waitlist entry per ordering policy. The
          system MUST handle offer expiration (entry does not respond
          within timeout) by advancing to the next entry. The system
          MUST enforce expiration_policy: removing entries that have
          exceeded their maximum wait time.
          Actors: ACT-T001, ACT-T003, ACT-T008.
```

### Service Metrics & Compliance

```
CAP-T031: The system MUST support TemporalServiceMetric (TERM-T021)
          computation and breach detection. The system MUST continuously
          measure temporal performance against configured thresholds
          (P50, P95, P99). When a breach is detected, the system MUST
          emit `substrate.temporal.service_metric.breached` for
          GOVERNANCE consumption. The system MUST track breach frequency
          and trend direction (improving/stable/degrading).
          Actors: ACT-T002, ACT-T007.

CAP-T032: The system MUST support SchedulingPolicy (TERM-T026) creation,
          validation, and enforcement. compliance-type policies MUST
          consume GOVERNANCE Norms with temporal_constraint_spec. The
          system MUST enforce SchedulingPolicies during Schedule creation
          and Booking creation — not only retroactively. When a
          scheduling operation would violate a SchedulingPolicy, the
          system MUST: (a) reject the operation if the policy is hard,
          (b) record the violation and proceed if the policy is soft,
          (c) emit `substrate.temporal.scheduling_policy.violated` for
          GOVERNANCE consumption in either case.
          Actors: ACT-T001, ACT-T002, ACT-T003, ACT-T004.
```

### AI Temporal Governance

```
CAP-T033: The system MUST support TemporalEnvelope (TERM-T025) creation
          and enforcement. AI agents operating without a TemporalEnvelope
          MUST have zero scheduling authority (no Booking creation, no
          Schedule modification, no Conflict resolution). The system
          MUST enforce all envelope constraints: max_scheduling_horizon,
          max_bookings_per_period, accessible_resource_pools,
          conflict_resolution_authority, constraint_relaxation_authority,
          and prohibited_operations. Envelope violations MUST be logged
          and rejected.
          Actors: ACT-T002.

CAP-T034: The system MUST support scheduling decision auditability. For
          every Booking, Schedule, and Resolution created by an AI agent,
          the system MUST record: the scheduling_rationale, the
          SchedulingObjective scores, the constraints considered, and
          the alternatives evaluated. An Auditor (ACT-T007) MUST be
          able to reconstruct the decision process for any AI-generated
          scheduling decision.
          Actors: ACT-T003, ACT-T004, ACT-T007.
```

---

## 5. DOMAIN OBJECTS & STATE (WHAT EXISTS AND HOW IT CHANGES)

> Every primitive from Section 3 has a corresponding entity definition here. Entity
> identifiers use the ENT-T prefix. State machines use SM-T. Together they form the
> complete data model of temporal coordination from first Calendar through final
> Schedule completion.

### 5.1 Temporal Containers & Interpretation Entities

```
ENT-T001: Calendar — Source: TERM-T001, SRC-T001, SRC-T003
  Purpose:        Named, timezone-aware temporal container defining working periods,
                  exceptions, and scheduling context.
  Attributes:
    - calendar_id         | UUID           | globally unique, immutable       | required
    - organization_id     | UUID           | scoping                         | required
    - name                | string         | ≤256 chars                       | required
    - description         | text           | —                               | optional
    - calendar_system_ref | ref ENT-T027   | interpretation rules             | required
    - default_timezone    | string         | IANA tz identifier               | required
    - working_periods     | list<ref ENT-T002> | normal availability windows  | required
    - exceptions          | list<object>   | {exception_id, name, date_range,
                            override_type, scope, availability_override,
                            recurrence_ref}                                    | optional
    - parent_calendar_ref | ref ENT-T001   | for hierarchical inheritance     | optional
    - scope               | enum: organization | department | team |
                            individual | resource_pool | location              | required
    - status              | enum: active | archived                           | required  | default: active
    - version             | integer        | monotonically increasing         | required  | default: 1
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      active → archived. New version = new Calendar version entity.
  Persistence:    Persistent, event-sourced. All versions retained.
  Ownership:      ACT-T002 (Temporal Steward) creates and manages.
  Relationships:  References ENT-T027 (CalendarSystem) — N:1
                  Parent/child hierarchy via parent_calendar_ref — tree
                  Contains ENT-T002 (TimeWindow) via working_periods — 1:N
                  Referenced by ENT-T016 (SchedulableResource) — 1:N
  Constraints:    Exceptions override working_periods at their scope level.
                  Child calendars inherit parent working_periods and may add exceptions.

ENT-T002: TimeWindow — Source: TERM-T002, SRC-T001, SRC-T009
  Purpose:        Bounded interval [start, end) with availability state.
  Attributes:
    - window_id           | UUID           | globally unique, immutable       | required
    - start               | timestamp      | UTC, inclusive                   | required
    - end                 | timestamp      | UTC, exclusive                   | required
    - duration            | duration       | computed: end - start            | computed
    - timezone            | string         | IANA tz for display              | required
    - availability_state  | enum: available | unavailable | tentative |
                            conditional | on_call | standby                    | required
    - recurrence_ref      | ref ENT-T005   | if this window repeats           | optional
    - conditions          | list<text>     | for conditional state            | optional
    - response_time       | duration       | for on_call state                | optional
    - activation_conditions | text         | for standby state                | optional
    - metadata            | object         | —                               | optional
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Immutable once created. Superseded by new TimeWindow on change.
  Persistence:    Persistent, event-sourced
  Ownership:      System computes. ACT-T001, ACT-T002 may create manually.
  Relationships:  Referenced by ENT-T001 (Calendar) — N:1
                  Referenced by ENT-T004 (Booking) — 1:1
                  Referenced by ENT-T003 (Availability) — 1:N
  Constraints:    start MUST be before end. Half-open interval: [start, end).
                  on_call requires response_time. standby requires activation_conditions.

ENT-T003: Availability — Source: TERM-T003, SRC-T001, SRC-T008
  Purpose:        Computed set of TimeWindows when a resource can accept Bookings.
  Attributes:
    - availability_id     | UUID           | globally unique                  | required
    - resource_ref        | ref ENT-T016   | whose availability               | required
    - computed_at         | timestamp      | when computation ran             | required
    - horizon_ref         | ref ENT-T012   | how far into the future          | required
    - windows             | list<ref ENT-T002> | available TimeWindows         | computed
    - capacity_per_window | list<object>   | {window_ref, total, committed,
                            available, unit_type}                              | computed
    - computation_inputs  | object         | {calendar_refs, booking_refs,
                            constraint_refs, capacity_ref}                     | required
    - visibility_level    | enum: full_detail | busy_free | slots_only        | required
    - cache_ttl           | duration       | validity period                  | required
  Identity:       UUID (computed output, versioned by computed_at)
  Lifecycle:      Computed on demand. Expires per cache_ttl. Re-computed on input change.
  Persistence:    Cached, re-computable from inputs. Not authoritative — inputs are.
  Ownership:      System computes. All actors may read per visibility_level.
  Relationships:  References ENT-T016 (SchedulableResource) — N:1
                  References ENT-T012 (Horizon) — N:1
                  Composed of ENT-T002 (TimeWindow) — 1:N
  Constraints:    visibility_level enforced per TRUST-T001 and TRUST-T004.
                  Cross-org: default busy_free only.

ENT-T005: Recurrence — Source: TERM-T005, SRC-T001, SRC-T009
  Purpose:        Declarative rule generating repeating TimeWindows or Bookings.
  Attributes:
    - recurrence_id       | UUID           | globally unique, immutable       | required
    - rule                | string         | RFC 5545 RRULE or extended syntax | required
    - effective_from      | timestamp      | start of recurrence              | required
    - effective_until     | timestamp      | end (null = indefinite)          | optional
    - exception_dates     | list<date>     | EXDATE exclusions                | optional
    - exception_rules     | list<string>   | EXRULE pattern exclusions        | optional
    - extensions          | object         | {rotating_shift, academic_term,
                            fiscal_period}                                     | optional
    - generated_count     | integer        | instances generated to date      | computed
    - next_occurrence     | timestamp      | next future instance             | computed
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Active while within effective date range. Instance generation is lazy.
  Persistence:    Persistent, event-sourced. Rule is authoritative; instances are computed.
  Ownership:      ACT-T001, ACT-T002, ACT-T003 create.
  Relationships:  Referenced by ENT-T002 (TimeWindow) — 1:N generated
                  Referenced by ENT-T018 (Shift) — 1:1
                  Referenced by ENT-T023 (Cadence) — 1:1
                  Sole owner of RFC 5545 RRULE interpretation (P4)
  Constraints:    RRULE parsing MUST handle all RFC 5545 frequencies plus extensions.
                  Unbounded recurrences (no COUNT/UNTIL) MUST be lazy-generated.

ENT-T027: CalendarSystem — Source: TERM-T027, SRC-T009
  Purpose:        Rules for interpreting dates/times including timezone and calendar type.
  Attributes:
    - calendar_system_id  | UUID           | globally unique, immutable       | required
    - name                | string         | e.g., "Gregorian/America/New_York" | required
    - type                | enum: gregorian | islamic_hijri | hebrew |
                            chinese_lunar | japanese_imperial | thai_buddhist |
                            fiscal_custom | iso_week                           | required
    - epoch_definition    | text           | reference point for year numbering | required
    - month_rules         | object         | how months determined             | required
    - leap_rules          | object         | when leap days/months inserted    | required
    - week_rules          | object         | {first_day_of_week, min_days_in_
                            first_week, weekend_days[]}                        | required
    - timezone_rules_ref  | string         | IANA tz database reference        | required
    - display_format      | object         | locale-specific formatting        | required
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Immutable once registered. Timezone rules update per IANA releases.
  Persistence:    Persistent. Reference data.
  Ownership:      ACT-T002 (Temporal Steward) registers.
  Relationships:  Referenced by ENT-T001 (Calendar) — 1:N
  Constraints:    All internal timestamp storage is UTC. CalendarSystem provides
                  interpretation for display and input only.
```

### 5.2 Activities & Structure Entities

```
ENT-T007: Activity — Source: TERM-T007, SRC-T002, SRC-T004, SRC-T006
  Purpose:        Unit of schedulable work with duration, resource requirements, and constraints.
  Attributes:
    - activity_id         | UUID           | globally unique, immutable       | required
    - organization_id     | UUID           | scoping                         | required
    - name                | string         | ≤256 chars                       | required
    - description         | text           | —                               | optional
    - activity_type       | enum: task | meeting | appointment | maintenance |
                            production | examination | hearing | event |
                            training | travel | custom                         | required
    - duration            | object         | {type: fixed|estimated|range,
                            value, min, expected, max}                         | required
    - resource_requirements | list<ref ENT-T017> | what resources needed      | optional
    - constraints         | list<ref ENT-T006> | temporal constraints          | optional
    - dependencies        | list<ref ENT-T009> | sequencing links              | optional
    - priority            | integer        | lower = higher priority          | required  | default: 100
    - deadline_ref        | ref ENT-T020   | temporal bound                   | optional
    - schedule_ref        | ref ENT-T010   | containing Schedule              | required
    - scheduling_rationale | text          | why this resource/time assigned  | required
    - knowledge_proposition_ref | UUID     | KNOWLEDGE TERM-K001 ref for v1.1 | optional
    - status              | enum per SM-T001                                   | required  | default: draft
    - actual_start        | timestamp      | when actually started            | optional
    - actual_end          | timestamp      | when actually ended              | optional
    - actual_duration     | duration       | computed from actuals            | computed
    - tags                | list<string>   | —                               | optional
    - metadata            | object         | —                               | optional
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      See SM-T001 (Activity Lifecycle)
  Persistence:    Persistent, event-sourced. All status transitions retained.
  Ownership:      ACT-T001 (Human Scheduler) or ACT-T003/T004 (AI Agent) creates.
  Relationships:  Belongs to ENT-T010 (Schedule) — N:1
                  Has ENT-T017 (ResourceRequirement) — 1:N
                  Has ENT-T009 (Dependency) as predecessor or successor — N:N
                  Has ENT-T006 (Constraint) — N:N
                  Assigned via ENT-T004 (Booking) — 1:N
                  May reference KNOWLEDGE Proposition (TERM-K001) — cross-substrate
                  Completion emits event for KNOWLEDGE duration analysis
  Constraints:    scheduling_rationale MUST be non-empty for all scheduled Activities.
                  estimated duration: min ≤ expected ≤ max.

ENT-T008: Milestone — Source: TERM-T008, SRC-T002
  Purpose:        Zero-duration schedule marker (deadline, handoff, gate, delivery).
  Attributes:
    - milestone_id        | UUID           | globally unique, immutable       | required
    - organization_id     | UUID           | scoping                         | required
    - name                | string         | ≤256 chars                       | required
    - milestone_type      | enum: deadline | handoff | gate | delivery |
                            phase_boundary | contractual | regulatory | custom  | required
    - target_date         | timestamp      | planned achievement date         | required
    - schedule_ref        | ref ENT-T010   | containing Schedule              | required
    - dependencies        | list<ref ENT-T009> | predecessor Activities        | optional
    - status              | enum: pending | achieved | missed | deferred       | required
    - achieved_date       | timestamp      | actual achievement date          | optional
    - variance            | duration       | target - achieved (computed)      | computed
    - escalation_rules    | list<object>   | action on miss                   | optional
    - source_ref          | UUID           | cross-substrate origin            | optional
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      pending → achieved | missed | deferred. Achieved/missed automatic on date.
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-T001 creates. System auto-transitions on date evaluation.
  Relationships:  Belongs to ENT-T010 (Schedule) — N:1
                  Has ENT-T009 (Dependency) — N:N

ENT-T009: Dependency — Source: TERM-T009, SRC-T002, SRC-T004
  Purpose:        Typed directed sequencing link between Activities.
  Attributes:
    - dependency_id       | UUID           | globally unique, immutable       | required
    - predecessor_ref     | ref ENT-T007   | preceding Activity               | required
    - successor_ref       | ref ENT-T007   | following Activity               | required
    - type                | enum: FS | SS | FF | SF                           | required  | default: FS
    - lag                 | duration       | positive=lag, negative=lead      | optional  | default: 0
    - constraint_type     | enum: hard | soft                                 | required  | default: hard
    - description         | text           | —                               | optional
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Active while both Activities exist. Removed on Activity cancellation.
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-T001 or ACT-T003/T004 creates.
  Relationships:  Links ENT-T007 (Activity) — N:N
  Constraints:    Dependency cycles MUST be detected and reported as Conflict (dependency_cycle).
                  predecessor_ref ≠ successor_ref.

ENT-T006: Constraint — Source: TERM-T006, SRC-T002, SRC-T009
  Purpose:        Temporal relationship beyond sequencing with hardness and relaxation support.
  Attributes:
    - constraint_id       | UUID           | globally unique, immutable       | required
    - organization_id     | UUID           | scoping                         | required
    - name                | string         | ≤256 chars                       | required
    - constraint_type     | enum: overlaps | simultaneous | mutex | proximity |
                            time_fence | resource_leveling | custom            | required
    - participants        | list<UUID>     | Activity and/or TimeWindow refs  | required
    - hardness            | enum: hard | soft | preference                    | required
    - violation_penalty   | numeric        | cost of violating (soft only)    | optional
    - relaxation_priority | integer        | order to relax (lower=relax last)| optional
    - relaxed_by          | ref ENT-T015   | Resolution that relaxed this     | optional
    - parameters          | object         | type-specific params             | optional
    - source_ref          | UUID           | cross-substrate origin            | optional
    - status              | enum: active | relaxed | suspended | archived     | required
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      active → relaxed (via Resolution) → active (if Resolution reversed).
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-T001, ACT-T002, ACT-T003, ACT-T004 create.
  Relationships:  Constrains ENT-T007 (Activity) and/or ENT-T002 (TimeWindow) — N:N
                  May be relaxed by ENT-T015 (Resolution) — N:1
                  May source from GOVERNANCE Norm (TERM-G001) — cross-substrate ref
  Constraints:    Hard constraints MUST NOT be automatically relaxed.
                  Soft constraint relaxation requires Resolution with justification.

ENT-T020: Deadline — Source: TERM-T020, SRC-T002, SRC-T011
  Purpose:        Temporal bound with escalation semantics on Activity/Milestone completion.
  Attributes:
    - deadline_id         | UUID           | globally unique, immutable       | required
    - target_ref          | UUID           | Activity or Milestone ref        | required
    - due                 | timestamp      | UTC                              | required
    - type                | enum: hard | soft                                 | required
    - escalation_rules    | list<object>   | {trigger_offset, action,
                            recipients[], message_template}                    | optional
    - notification_triggers | list<object> | {offset, channel, recipients[]}  | optional
    - source_ref          | UUID           | cross-substrate origin            | optional
    - status              | enum: pending | approaching | met | breached |
                            waived                                             | required  | default: pending
    - breach_timestamp    | timestamp      | when breached                    | optional
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      pending → approaching → met | breached. waived by authority.
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-T001, ACT-T003 create. System auto-transitions.
  Relationships:  Targets ENT-T007 (Activity) or ENT-T008 (Milestone) — N:1
                  May source from COMMUNICATION Commitment (TERM-M005) — cross-substrate
                  May source from GOVERNANCE Obligation (TERM-G005) — cross-substrate
```

### 5.3 Scheduling & Plans Entities

```
ENT-T010: Schedule — Source: TERM-T010, SRC-T002, SRC-T003, SRC-T004
  Purpose:        Consistent assignment of Activities to TimeWindows and Resources.
  Attributes:
    - schedule_id         | UUID           | globally unique, immutable       | required
    - organization_id     | UUID           | scoping                         | required
    - name                | string         | ≤256 chars                       | required
    - schedule_type       | enum: project | workforce | production |
                            appointment | resource_booking | maintenance |
                            custom                                             | required
    - horizon_ref         | ref ENT-T012   | temporal boundary                | required
    - activities          | list<ref ENT-T007> | constituent Activities        | computed
    - dependencies        | list<ref ENT-T009> | sequencing links              | computed
    - constraints         | list<ref ENT-T006> | temporal constraints          | computed
    - bookings            | list<ref ENT-T004> | resource assignments           | computed
    - milestones          | list<ref ENT-T008> | schedule markers               | optional
    - feasibility_status  | enum: feasible | infeasible | relaxed             | required
    - quality_scores      | list<object>   | {objective_ref, score, unit}     | optional
    - optimality_bound    | numeric        | solver-provided quality bound    | optional
    - comparison_baseline | ref ENT-T011   | Timeline for comparison          | optional
    - solver_ref          | UUID           | COMPUTE Pipeline ref             | optional
    - policies            | list<ref ENT-T026> | applied SchedulingPolicies    | optional
    - status              | enum per SM-T003                                   | required  | default: draft
    - version             | integer        | monotonically increasing         | required  | default: 1
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
    - last_modified_at    | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      See SM-T003 (Schedule Lifecycle)
  Persistence:    Persistent, event-sourced. Timelines capture every version.
  Ownership:      ACT-T001 or ACT-T003/T004 creates. ACT-T002 configures policies.
  Relationships:  Contains ENT-T007 (Activity) — 1:N
                  Contains ENT-T004 (Booking) — 1:N
                  Versioned via ENT-T011 (Timeline) — 1:N
                  Uses ENT-T012 (Horizon) — N:1
                  Applies ENT-T026 (SchedulingPolicy) — N:N
  Constraints:    feasibility_status=feasible requires all hard Constraints satisfied.
                  feasibility_status=relaxed requires Resolution records for each relaxation.

ENT-T011: Timeline — Source: TERM-T011, SRC-T002, SRC-T016
  Purpose:        Immutable snapshot of a Schedule at a point in time.
  Attributes:
    - timeline_id         | UUID           | globally unique, immutable       | required
    - schedule_ref        | ref ENT-T010   | source Schedule                  | required
    - snapshot_timestamp  | timestamp      | when snapshot taken              | required
    - version             | integer        | corresponds to Schedule version  | required
    - activity_assignments | list<object>  | {activity_ref, timewindow,
                            resource_ref, status_at_snapshot}                  | required
    - constraint_state    | list<object>   | {constraint_ref, satisfied,
                            relaxed}                                           | required
    - critical_path       | list<ref ENT-T007> | ordered Activity refs        | computed
    - slack_per_activity  | list<object>   | {activity_ref, total_slack,
                            free_slack}                                        | computed
    - delta_from_previous | object         | structured diff from prior       | optional
    - hash                | string         | integrity hash                   | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      IMMUTABLE. Created once. Never modified. Never deleted.
  Persistence:    Persistent, append-only, immutable. Retained for audit.
  Ownership:      System creates on each Schedule modification.
  Relationships:  Snapshots ENT-T010 (Schedule) — N:1
  Constraints:    Append-only. Any modification = system integrity violation.

ENT-T012: Horizon — Source: TERM-T012, SRC-T002
  Purpose:        Temporal boundary and resolution of a Schedule.
  Attributes:
    - horizon_id          | UUID           | globally unique, immutable       | required
    - start               | timestamp      | horizon start                    | required
    - end                 | timestamp      | horizon end                      | required
    - type                | enum: operational | tactical | strategic           | required
    - resolution          | object         | {granularity, scheduling_precision} | required
    - rolling_window      | object         | {advance_frequency, advance_amount} | optional
    - update_frequency    | duration       | re-optimization frequency        | required
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Rolling horizons advance automatically. Static horizons fixed.
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-T002 (Temporal Steward) configures.
  Relationships:  Referenced by ENT-T010 (Schedule) — 1:N
                  Referenced by ENT-T003 (Availability) — 1:N
                  Referenced by ENT-T028 (Capacity) — 1:N

ENT-T022: Buffer — Source: TERM-T022, SRC-T002
  Purpose:        Explicitly allocated slack for schedule protection.
  Attributes:
    - buffer_id           | UUID           | globally unique, immutable       | required
    - buffer_type         | enum: feeding | project | resource | time_between |
                            custom                                             | required
    - duration            | duration       | allocated buffer time            | required
    - placement           | object         | {before_ref, after_ref,
                            at_boundary}                                       | required
    - consumption_tracking | object        | {original_duration, remaining,
                            consumption_rate}                                  | computed
    - schedule_ref        | ref ENT-T010   | containing Schedule              | required
    - rationale           | text           | why this buffer exists           | required
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Active while Schedule active. Consumed as activities use slack.
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-T001 or ACT-T003/T004 creates.
  Relationships:  Belongs to ENT-T010 (Schedule) — N:1
                  References ENT-T007 (Activity) or ENT-T008 (Milestone) for placement
```

### 5.4 Bookings & Resources Entities

```
ENT-T004: Booking — Source: TERM-T004, SRC-T001, SRC-T008, SRC-T015
  Purpose:        Confirmed allocation of SchedulableResource to Activity during TimeWindow.
  Attributes:
    - booking_id          | UUID           | globally unique, immutable       | required
    - organization_id     | UUID           | scoping                         | required
    - activity_ref        | ref ENT-T007   | what is being done               | required
    - resource_ref        | ref ENT-T016   | who/what is doing it             | required
    - timewindow          | ref ENT-T002   | when it happens                  | required
    - schedule_ref        | ref ENT-T010   | containing Schedule              | required
    - booking_type        | enum: confirmed | tentative | held | waitlisted   | required
    - scheduling_rationale | text          | why this assignment (mandatory)  | required
    - commercial_agreement_ref | UUID      | BUSINESS Reservation TERM-023    | optional
    - confirmation_timestamp | timestamp   | when confirmed                   | optional
    - hold_expiry         | timestamp      | for held bookings                | optional
    - status              | enum per SM-T002                                   | required  | default: requested
    - cancellation_reason | text           | if cancelled                     | optional
    - version             | integer        | monotonically increasing         | required  | default: 1
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      See SM-T002 (Booking Lifecycle)
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-T001, ACT-T003, ACT-T004 create. ACT-T008 may request.
  Relationships:  Links ENT-T007 (Activity) to ENT-T016 (SchedulableResource) — bridge
                  Uses ENT-T002 (TimeWindow) — N:1
                  Belongs to ENT-T010 (Schedule) — N:1
                  May reference BUSINESS Reservation (TERM-023) — cross-substrate
  Constraints:    scheduling_rationale MUST be non-empty.
                  Double-booking prevention: CONC-T001.
                  hold_expiry auto-releases on expiry.

ENT-T016: SchedulableResource — Source: TERM-T016, SRC-T003, SRC-T008
  Purpose:        Entity with temporal availability assignable to Activities via Bookings.
  Attributes:
    - resource_id         | UUID           | globally unique, immutable       | required
    - organization_id     | UUID           | scoping                         | required
    - name                | string         | ≤256 chars                       | required
    - resource_type       | enum: person | equipment | room | vehicle |
                            compute | facility | generic                       | required
    - calendar_refs       | list<ref ENT-T001> | defining working periods     | required
    - availability_ref    | ref ENT-T003   | computed availability            | computed
    - capacity_level      | object         | {total, unit_type}               | required
    - skills              | list<object>   | {skill_name, proficiency_level}  | optional
    - location            | object         | for co-location constraints      | optional
    - preference_declarations | list<object> | {preference_type, value,
                            priority, legal_basis}                             | optional
    - physical_asset_ref  | UUID           | PHYSICAL PhysicalAsset TERM-P003 | optional
    - cost_rate           | object         | BUSINESS-owned, referenced       | optional
    - status              | enum: active | inactive | on_leave |
                            decommissioned                                     | required  | default: active
    - tags                | list<string>   | —                               | optional
    - metadata            | object         | —                               | optional
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      active → inactive | on_leave → active. decommissioned is terminal.
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-T002 registers. ACT-T005 declares preferences.
  Relationships:  References ENT-T001 (Calendar) — N:N
                  Produces ENT-T003 (Availability) — 1:1
                  Assigned via ENT-T004 (Booking) — 1:N
                  May link to PHYSICAL PhysicalAsset (TERM-P003) — cross-substrate
  Constraints:    Status change creates Disruption for affected Bookings.
                  preference_declarations with priority=hard_constraint are enforced;
                  priority=preference are best-effort.

ENT-T017: ResourceRequirement — Source: TERM-T017, SRC-T003, SRC-T004
  Purpose:        Declarative specification of what resources an Activity needs.
  Attributes:
    - requirement_id      | UUID           | globally unique, immutable       | required
    - activity_ref        | ref ENT-T007   | requesting Activity              | required
    - quantity            | integer        | how many resources               | required
    - resource_type       | enum           | matching SchedulableResource types | required
    - required_skills     | list<object>   | {skill_name, minimum_proficiency} | optional
    - duration_override   | duration       | if resource needed for subset    | optional
    - synchronization_mode | enum: all_simultaneous | sequential |
                            any_subset                                         | required  | default: all_simultaneous
    - co_location_required | boolean       | same location needed             | required  | default: false
    - temporal_alignment  | enum: exact_overlap | partial_overlap | adjacent   | required  | default: exact_overlap
    - substitution_rules  | list<object>   | alternative specs if unavailable | optional
    - priority            | integer        | assignment ordering              | required  | default: 100
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Active while parent Activity exists.
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-T001, ACT-T003, ACT-T004 create.
  Relationships:  Belongs to ENT-T007 (Activity) — N:1
                  Resolved by ENT-T004 (Booking) — 1:N
```

### 5.5 Workforce, Conflicts, Capacity & Policy Entities

```
ENT-T018: Shift — Source: TERM-T018, SRC-T003
  Attributes:     shift_id (UUID), organization_id, name, shift_type, start_time,
                  end_time, duration (computed), break_rules[], recurrence_ref,
                  rotation_ref, eligibility_rules[], resource_requirements[],
                  labor_constraints[], premium_multiplier, status, created_by, created_at.
  Lifecycle:      active → inactive.
  Ownership:      ACT-T002 defines. ACT-T001 assigns.
  Relationships:  Uses ENT-T005 (Recurrence), belongs to ENT-T019 (Rotation).

ENT-T019: Rotation — Source: TERM-T019, SRC-T003
  Attributes:     rotation_id (UUID), organization_id, name, rotation_type,
                  resource_pool[], shift_pattern[], cycle_length, fairness_metrics
                  (computed: distribution_equity, weekend_equity, holiday_equity,
                  preference_satisfaction), rebalance_trigger, status, created_by, created_at.
  Lifecycle:      active → paused → active. completed when cycle ends.
  Ownership:      ACT-T002 defines. System computes fairness_metrics.
  Relationships:  Contains ENT-T018 (Shift) — 1:N. Pools ENT-T016 (SchedulableResource) — N:N.

ENT-T023: Cadence — Source: TERM-T023, SRC-T002
  Attributes:     cadence_id (UUID), organization_id, name, purpose, recurrence_ref,
                  cycle_length, boundary_rules[], phase_within_cadence[],
                  alignment_rules[], status, created_by, created_at.
  Lifecycle:      active → paused → archived.
  Ownership:      ACT-T002 defines.
  Relationships:  Uses ENT-T005 (Recurrence). Generates ENT-T007 (Activity) at boundaries.

ENT-T014: Conflict — Source: TERM-T014, SRC-T016
  Attributes:     conflict_id (UUID), conflict_type, conflicting_entities[],
                  resource_ref, timewindow, severity, detected_at, detected_by,
                  resolution_ref, status (per SM-T004), created_at.
  Lifecycle:      See SM-T004 (Conflict Lifecycle).
  Ownership:      System detects. ACT-T001, ACT-T003, ACT-T004 resolve.
  Relationships:  References conflicting ENT-T004/ENT-T007/ENT-T006. Resolved by ENT-T015.

ENT-T015: Resolution — Source: TERM-T015, SRC-T016
  Attributes:     resolution_id (UUID), conflict_ref, resolution_type, authority,
                  justification, affected_bookings[], affected_activities[],
                  affected_parties_notified, notification_refs[], reversible,
                  reversal_deadline, constraint_relaxed_ref, status, created_by, created_at.
  Lifecycle:      proposed → approved → applied → reversed (optional).
  Ownership:      ACT-T001, ACT-T003, ACT-T004 propose. Authority approves.
  Relationships:  Resolves ENT-T014 (Conflict). May relax ENT-T006 (Constraint).

ENT-T013: Disruption — Source: TERM-T013, SRC-T016
  Attributes:     disruption_id (UUID), disruption_type, source, affected_schedule_ref,
                  affected_activities[], cascade_analysis (computed: cascade_depth,
                  cascade_breadth, affected_resources[], estimated_recovery_time),
                  rescheduling_recommendation, severity, response_deadline,
                  status (per SM-T005), created_at.
  Lifecycle:      See SM-T005 (Disruption Lifecycle).
  Ownership:      System creates from events. ACT-T001, ACT-T003, ACT-T004 respond.
  Relationships:  Affects ENT-T010 (Schedule). References ENT-T007 (Activity).

ENT-T028: Capacity — Source: TERM-T028, SRC-T003, SRC-T004
  Attributes:     capacity_id (UUID), organization_id, resource_pool_ref, horizon_ref,
                  time_buckets[] (period_start, period_end, total_units, committed_units,
                  available_units, utilization_rate), unit_type, demand_forecast_ref,
                  supply_constraints[], gap_analysis (computed), snapshot_timestamp,
                  created_by, created_at.
  Lifecycle:      Computed on demand. Snapshot at point-in-time.
  Ownership:      ACT-T001, ACT-T002, ACT-T004 compute.
  Relationships:  Pools ENT-T016 (SchedulableResource). Uses ENT-T012 (Horizon).

ENT-T029: TransitionTime — Source: TERM-T029, SRC-T004, SRC-T006
  Attributes:     transition_id (UUID), from_activity_type, to_activity_type,
                  resource_ref, minimum_duration, typical_duration, includes[],
                  sequence_dependent, travel_details, created_by, created_at.
  Lifecycle:      Reference data. Updated by ACT-T002.
  Ownership:      ACT-T002 configures.
  Relationships:  References ENT-T016 (SchedulableResource). Consumed by Availability computation.

ENT-T030: Waitlist — Source: TERM-T030, SRC-T006, SRC-T015
  Attributes:     waitlist_id (UUID), organization_id, name, resource_or_service_ref,
                  entries[] (entry_id, requestor, requested_preferences, priority,
                  position (computed), enrollment_timestamp, expiration_policy,
                  callback_trigger, status), ordering_policy, notification_policy,
                  max_size, created_by, created_at.
  Lifecycle:      Active while entries exist. Entries: active → offered → accepted | expired | withdrawn.
  Ownership:      ACT-T001 manages. ACT-T008 enrolls.
  Relationships:  References ENT-T016 (SchedulableResource). Converts to ENT-T004 (Booking).

ENT-T024: SchedulingObjective — Source: TERM-T024, SRC-T009
  Attributes:     objective_id (UUID), organization_id, name, description, metric,
                  direction, weight, measurement_method, target_value, acceptable_range,
                  created_by, created_at.
  Lifecycle:      Reference data. Active while organization uses.
  Ownership:      ACT-T002 defines.
  Relationships:  Referenced by ENT-T010 (Schedule) via quality_scores.

ENT-T021: TemporalServiceMetric — Source: TERM-T021, SRC-T016
  Attributes:     metric_id (UUID), organization_id, name, metric_type, target_duration,
                  threshold_percentiles, measurement_window, current_performance,
                  breach_detected, breach_timestamp, breach_count_in_window, trend,
                  obligation_ref, created_by, created_at.
  Lifecycle:      Continuously computed. Breach detection automatic.
  Ownership:      ACT-T002 configures targets. System computes performance.
  Relationships:  May reference GOVERNANCE Obligation (TERM-G005) — cross-substrate.

ENT-T026: SchedulingPolicy — Source: TERM-T026, SRC-T003, SRC-T009
  Attributes:     policy_id (UUID), organization_id, name, description, policy_type,
                  parameters (type-specific), scope, effective_from, effective_until,
                  legal_basis, status, created_by, created_at.
  Lifecycle:      active → suspended → archived. Effective within date range.
  Ownership:      ACT-T002 creates. Consumes GOVERNANCE Norms for compliance type.
  Relationships:  Applied to ENT-T010 (Schedule) — N:N.
                  compliance type references GOVERNANCE Norm (TERM-G001) — cross-substrate.

ENT-T025: TemporalEnvelope — Source: TERM-T025, ASM-T005
  Attributes:     envelope_id (UUID), organization_id, agent_id, max_scheduling_horizon,
                  max_bookings_per_period, accessible_resource_pools[],
                  conflict_resolution_authority, constraint_relaxation_authority,
                  override_limits, schedule_types_allowed[], prohibited_operations[],
                  parent_envelope_ref, effective_from, effective_until, created_by, created_at.
  Lifecycle:      active → suspended → expired | revoked. Auto-expires.
  Persistence:    Persistent, event-sourced. MUST NOT be self-granted by AI.
  Ownership:      Human Authority grants (ACT-T002).
  Relationships:  Chains from Epistemic Envelope (TERM-K022) — downstream
                  Chains to DesignEnvelope (TERM-D025) — upstream
  Constraints:    effective_until MUST be set. Maximum duration: organization-configured.
                  prohibited_operations MUST include all operations beyond authority level.
```

### 5.6 State Machines

```
SM-T001: Activity Lifecycle — Governs: ENT-T007 — Source: TERM-T007, SRC-T002
  States:     draft → scheduled → in_progress → completed | cancelled | deferred
  Transitions:
    draft → scheduled:       Activity assigned to Schedule, Bookings created, all
                             ResourceRequirements satisfied. scheduling_rationale set.
    scheduled → in_progress: Actual_start timestamp recorded. Activity execution begins.
    in_progress → completed: Actual_end timestamp recorded. Duration captured.
                             Emits `substrate.temporal.activity.completed` with actual
                             duration for KNOWLEDGE consumption.
    scheduled → cancelled:   Activity removed from Schedule. Bookings released.
                             Dependent Activities re-evaluated. Cancellation_reason recorded.
    in_progress → cancelled: Activity stopped before completion. Partial work recorded.
    scheduled → deferred:    Activity postponed to future Schedule or indefinitely.
                             Bookings released. May be rescheduled later.
    deferred → draft:        Deferred Activity reactivated for rescheduling.
  Guards:
    draft → scheduled:       All hard Constraints satisfied. ResourceRequirements met.
    in_progress → completed: actual_end MUST be set.
    → cancelled:             cancellation_reason MUST be provided.

SM-T002: Booking Lifecycle — Governs: ENT-T004 — Source: TERM-T004, SRC-T001, SRC-T008
  States:     requested → confirmed → active → completed | cancelled | no_show
              requested → tentative → confirmed | released
              requested → held → confirmed | expired
  Transitions:
    requested → confirmed:   Resource available. No conflicts. scheduling_rationale set.
                             Emits `substrate.temporal.booking.confirmed`.
    requested → tentative:   Provisionally held. May be displaced by higher-priority
                             Booking per preemption SchedulingPolicy.
    requested → held:        Temporarily reserved. hold_expiry set.
    tentative → confirmed:   Confirmed after negotiation or priority resolution.
    tentative → released:    Displaced by higher-priority Booking. Slot freed.
    held → confirmed:        Hold converted to confirmed Booking before expiry.
    held → expired:          hold_expiry reached without confirmation. Slot freed.
                             Waitlist notified if applicable.
    confirmed → active:      Booking time window started. Activity in_progress.
    active → completed:      Booking time window ended. Activity completed normally.
    confirmed → cancelled:   Booking cancelled before start. Resource freed.
                             Emits `substrate.temporal.booking.cancelled`.
                             Waitlist notified if applicable.
    active → no_show:        Booking time window started but participant absent.
                             No-show recorded for historical analysis. Resource
                             may be reassigned.
  Guards:
    requested → confirmed:   Resource Availability verified. No Conflict detected.
    → cancelled:             cancellation_reason MUST be provided.
    active → no_show:        No-show detection threshold elapsed (configurable).

SM-T003: Schedule Lifecycle — Governs: ENT-T010 — Source: TERM-T010, SRC-T002
  States:     draft → computing → active → frozen → completed | archived
  Transitions:
    draft → computing:       Schedule submitted to solver via COMPUTE Pipeline.
                             Activities, Dependencies, Constraints, Resources assembled
                             into SchedulingProblem.
    computing → active:      Solver returns feasible SchedulingSolution. Bookings created.
                             Timeline snapshot taken. feasibility_status set.
    computing → draft:       Solver returns infeasible. Infeasibility explanation provided.
                             Human review required for constraint relaxation.
    active → active:         Schedule modified (Activity added/removed, Disruption processed,
                             Booking changed). New Timeline snapshot taken. Version incremented.
                             This is the NORMAL operation — schedules are continuously revised
                             (ASM-T003, Property T3).
    active → frozen:         Schedule locked for execution. No further modifications without
                             explicit unfreeze. Used for imminent execution windows.
    frozen → active:         Schedule unfrozen for modification. Typically triggered by
                             critical Disruption during frozen period.
    active → completed:      All Activities completed or cancelled. No pending work.
    active → archived:       Schedule superseded or no longer relevant. Retained for history.
    frozen → completed:      All Activities in frozen window completed.
  Guards:
    computing → active:      feasibility_status ∈ {feasible, relaxed}. All hard Constraints met.
    active → frozen:         Authority required (ACT-T001 or ACT-T002).

SM-T004: Conflict Lifecycle — Governs: ENT-T014 — Source: TERM-T014
  States:     detected → acknowledged → resolving → resolved | accepted
  Transitions:
    detected → acknowledged: Conflict surfaced to responsible actor. Assignment begun.
    acknowledged → resolving: Resolution in progress. Options evaluated.
    resolving → resolved:    Resolution (ENT-T015) applied. Conflicting entities updated.
                             Emits `substrate.temporal.conflict.resolved`.
    resolving → accepted:    Conflict intentionally accepted (e.g., overbooking policy).
                             accept_conflict Resolution created with justification.
    detected → resolved:     Auto-resolved by AI agent within TemporalEnvelope authority
                             (minor conflicts, auto-reschedule enabled).
  Guards:
    resolving → resolved:    Resolution MUST have authority and justification.
    resolving → accepted:    accept_conflict MUST have justification and authority.

SM-T005: Disruption Lifecycle — Governs: ENT-T013 — Source: TERM-T013, ASM-T003
  States:     detected → assessing → responding → recovered | unrecoverable
  Transitions:
    detected → assessing:    cascade_analysis computation initiated. Affected Activities,
                             Resources, and Schedules identified.
    assessing → responding:  cascade_analysis complete. Rescheduling options evaluated.
                             rescheduling_recommendation generated.
    responding → recovered:  Resolutions applied. All affected Schedules updated.
                             New Timelines created. Normal operation resumed.
    responding → unrecoverable: No feasible rescheduling exists. Human escalation required.
                             Affected Activities may need cancellation or deferral.
    detected → responding:   Auto-response for minor Disruptions per SchedulingPolicy
                             disruption_response configuration.
  Guards:
    responding → recovered:  All affected Schedules MUST have valid feasibility_status.
    responding → unrecoverable: All Resolution options evaluated and found infeasible.
```

---

## 6. INTERFACES (HOW EXTERNAL SYSTEMS INTERACT)

> Interface identifiers use IFC-T prefix. Each interface defines how
> external actors and systems interact with TEMPORAL through structured
> operations.

```
IFC-T001: Calendar Management Interface
          Operations: createCalendar, updateCalendar, addException,
                      removeException, getCalendar, listCalendars,
                      getEffectiveWorkingPeriods (resolves inheritance).
          Consumers:  ACT-T002 (Temporal Steward), ACT-T006 (External System).
          Protocol:   Synchronous request/response.
          Notes:      Import from iCalendar (RFC 5545) via ONBOARD-T001.
                      Export to iCalendar for interoperability.

IFC-T002: Availability Query Interface
          Operations: getAvailability (resource, horizon, visibility_level),
                      getMultiResourceAvailability (resources[], horizon,
                      synchronization_mode — the multi-resource intersection
                      operation from CAP-T018), getSlots (resource,
                      duration_needed, horizon — returns bookable time slots).
          Consumers:  ACT-T001, ACT-T003, ACT-T004, ACT-T005, ACT-T008.
          Protocol:   Synchronous request/response. Cached per Availability.cache_ttl.
          Notes:      visibility_level enforced per caller trust level.
                      Cross-org queries default to busy_free (TRUST-T004).
                      Multi-resource intersection is the computationally
                      hardest query (Property T2). Implementations SHOULD
                      optimize this path.

IFC-T003: Booking Interface
          Operations: createBooking, confirmBooking, cancelBooking,
                      modifyBooking, getBooking, listBookings (by resource,
                      by schedule, by time range).
          Consumers:  ACT-T001, ACT-T003, ACT-T004, ACT-T008.
          Protocol:   Synchronous request/response with optimistic concurrency
                      (CONC-T001). Conflict detection on create/modify.
          Notes:      createBooking requires scheduling_rationale.
                      Conflict detection is mandatory, not optional.
                      Waitlist integration: cancelled booking triggers
                      Waitlist offer.

IFC-T004: Schedule Management Interface
          Operations: createSchedule, submitToSolver, getSchedule,
                      modifySchedule, freezeSchedule, unfreezeSchedule,
                      getTimeline, compareTimelines, assessFeasibility.
          Consumers:  ACT-T001, ACT-T003, ACT-T004.
          Protocol:   submitToSolver is asynchronous (COMPUTE Pipeline execution).
                      All others synchronous request/response.
          Notes:      submitToSolver packages SchedulingProblem, submits to
                      COMPUTE, returns SchedulingSolution. See INT-T002.

IFC-T005: Disruption & Conflict Interface
          Operations: reportDisruption, getDisruption, getCascadeAnalysis,
                      reportConflict, getConflict, proposeResolution,
                      approveResolution, applyResolution, getResolution.
          Consumers:  ACT-T001, ACT-T003, ACT-T004, ACT-T006.
          Protocol:   Synchronous request/response. Disruption triggers
                      asynchronous cascade analysis.
          Notes:      Cross-substrate Disruptions created from events
                      (PHYSICAL, COMMUNICATION, GOVERNANCE). Internal
                      Disruptions created from Booking/Activity changes.

IFC-T006: Workforce Management Interface
          Operations: createShift, createRotation, assignShift,
                      getRotationFairness, rebalanceRotation, createCadence,
                      getCadencePhases.
          Consumers:  ACT-T001, ACT-T002, ACT-T003.
          Protocol:   Synchronous request/response.
          Notes:      Fairness metrics available to ACT-T007 via read-only
                      query. Labor constraint validation on every assignment.

IFC-T007: Capacity & Waitlist Interface
          Operations: computeCapacity, getCapacityGapAnalysis, createWaitlist,
                      enrollInWaitlist, getWaitlistPosition, offerSlot,
                      acceptOffer, withdrawFromWaitlist.
          Consumers:  ACT-T001, ACT-T002, ACT-T004, ACT-T008.
          Protocol:   Synchronous request/response.
          Notes:      Gap analysis consumed by BUSINESS for procurement.
                      Waitlist offers have configurable expiration.

IFC-T008: Service Metric Interface
          Operations: configureMetric, getMetricPerformance, getMetricTrend,
                      listBreaches.
          Consumers:  ACT-T002, ACT-T007.
          Protocol:   Synchronous request/response. Breach events emitted
                      asynchronously.
          Notes:      GOVERNANCE consumes breach events per INT-T004.

IFC-T009: Policy Management Interface
          Operations: createPolicy, updatePolicy, suspendPolicy, getPolicy,
                      listPolicies, validateScheduleAgainstPolicies.
          Consumers:  ACT-T002.
          Protocol:   Synchronous request/response.
          Notes:      compliance-type policies require GOVERNANCE Norm reference.

IFC-T010: Envelope Management Interface
          Operations: createEnvelope, getEnvelope, modifyEnvelope,
                      revokeEnvelope, validateAgentOperation.
          Consumers:  ACT-T002.
          Protocol:   Synchronous request/response. validateAgentOperation
                      called on every AI scheduling operation.
          Notes:      Envelopes MUST NOT be self-created or self-modified by
                      AI agents. Human authority required.
```

---

## 7. DATA FLOWS (HOW INFORMATION MOVES)

> Data flow identifiers use FLOW-T prefix. Each flow describes a
> multi-step process crossing entity boundaries within TEMPORAL or
> across substrates.

```
FLOW-T001: Single Booking Flow
  Trigger:    ACT-T001 or ACT-T008 requests a Booking.
  Steps:
    1. Validate TemporalEnvelope (if AI actor).
    2. Query Availability (IFC-T002) for target resource.
    3. Check Constraints applicable to the resource+timewindow.
    4. Check SchedulingPolicies (overbooking limits, preemption rules).
    5. Detect Conflicts (double-booking, capacity exceeded).
    6. If Conflict detected: surface Conflict, propose Resolution.
    7. If no Conflict: create Booking (ENT-T004) with scheduling_rationale.
    8. Update Availability cache (invalidate for affected resource).
    9. Emit `substrate.temporal.booking.confirmed`.
    10. If commercial: BUSINESS creates Reservation referencing Booking.
  Output:     Confirmed Booking or Conflict requiring resolution.

FLOW-T002: Schedule Generation Flow
  Trigger:    ACT-T001 or ACT-T004 requests Schedule creation.
  Steps:
    1. Assemble Activities, Dependencies, Constraints, ResourceRequirements.
    2. Collect SchedulingPolicies applicable to scope.
    3. Collect SchedulingObjectives.
    4. Package as SchedulingProblem (INT-T002 schema).
    5. Submit to COMPUTE Pipeline via IFC-T004.submitToSolver.
    6. COMPUTE allocates Resources, executes solver.
    7. Receive SchedulingSolution.
    8. Validate solution: all hard Constraints satisfied?
    9a. If feasible: create Schedule (ENT-T010), create Bookings,
        create Timeline snapshot, set feasibility_status.
    9b. If infeasible: report unsatisfiable Constraints, return to draft.
    10. Emit `substrate.temporal.schedule.created`.
  Output:     Active Schedule with Bookings and Timeline, or infeasibility report.

FLOW-T003: Disruption Handling Flow
  Trigger:    Disruption detected (internal or cross-substrate event).
  Steps:
    1. Create Disruption (ENT-T013) with type and source.
    2. Compute cascade_analysis: affected Activities, Resources, Schedules.
    3. Evaluate severity and response_deadline.
    4. Per SchedulingPolicy disruption_response:
       4a. immediate: auto-generate rescheduling recommendation.
       4b. within_hour: queue for near-term response.
       4c. next_cycle: defer to next Horizon update.
       4d. manual: surface to ACT-T001 for human decision.
    5. Generate Resolution candidates (reschedule, reassign, defer, cancel).
    6. Apply approved Resolution(s).
    7. Create new Timeline snapshot capturing post-disruption state.
    8. Notify affected parties via COMMUNICATION.
    9. Emit `substrate.temporal.disruption.recovered` or
       `substrate.temporal.disruption.unrecoverable`.
  Output:     Updated Schedule with new Timeline, or escalation to human authority.

FLOW-T004: Meeting Scheduling Flow (Cross-Substrate)
  Trigger:    Request to schedule a meeting with multiple participants.
  Steps:
    1. Create Activity (activity_type: meeting) with ResourceRequirements
       (all participants as SchedulableResources, synchronization_mode:
       all_simultaneous).
    2. Query multi-resource Availability (IFC-T002) for all participants.
    3. Identify feasible TimeWindows where all are available.
    4. Apply SchedulingPolicy preferences (preferred times, room preferences).
    5. Create Bookings for all participants and room.
    6. Emit `substrate.temporal.booking.confirmed`.
    7. COMMUNICATION creates Discourse instance for the meeting
       (discourse_template_ref on Activity).
    8. If participant declines (COMMUNICATION speech act):
       8a. COMMUNICATION emits decline event.
       8b. TEMPORAL creates Disruption (resource_unavailable).
       8c. FLOW-T003 (Disruption Handling) executes.
  Output:     Confirmed meeting with all participant Bookings + COMMUNICATION Discourse.

FLOW-T005: Maintenance Scheduling Flow (Cross-Substrate)
  Trigger:    PHYSICAL emits `substrate.physical.asset.degraded` or
              scheduled preventive maintenance cycle.
  Steps:
    1. TEMPORAL creates Activity (activity_type: maintenance) with
       ResourceRequirements (technician + equipment + parts).
    2. Query Availability for required resources.
    3. Apply Constraints (maintenance window from Calendar, safety constraints
       from GOVERNANCE Norms).
    4. Create Bookings for technician and equipment time.
    5. Emit `substrate.temporal.booking.confirmed`.
    6. At scheduled time: PHYSICAL executes ProcessExecution (TERM-P012)
       and MaintenanceAction (TERM-P021).
    7. On completion: PHYSICAL emits completion event → TEMPORAL
       transitions Activity to completed.
  Output:     Scheduled maintenance with temporal allocation + PHYSICAL execution plan.

FLOW-T006: Production Schedule Generation Flow (Cross-Substrate)
  Trigger:    BUSINESS demand signal (order received, forecast updated) +
              DESIGN BOM (TERM-D021) + FabricationMethod (TERM-D020).
  Steps:
    1. DESIGN provides BOM (components, quantities) and FabricationMethod
       (process sequences, equipment requirements, setup times).
    2. BUSINESS provides demand signals (quantities, delivery dates, priorities).
    3. TEMPORAL generates: Activities (per manufacturing step per BOM line),
       Dependencies (from process sequences), ResourceRequirements (from
       equipment/tooling specs), TransitionTimes (from setup/changeover data),
       Deadlines (from delivery dates).
    4. TEMPORAL assembles SchedulingProblem with production-specific
       SchedulingObjectives (minimize makespan, maximize throughput,
       minimize changeover time).
    5. Submit to solver via COMPUTE (FLOW-T002 steps 4-9).
    6. Validate production Schedule against capacity constraints.
    7. If capacity gap: emit gap_analysis for BUSINESS procurement.
  Output:     Production Schedule with work order Activities, equipment Bookings,
              and delivery Milestones.

FLOW-T007: Design Review Scheduling Flow (Cross-Substrate)
  Trigger:    DESIGN emits `substrate.design.review.scheduling_requested`.
  Steps:
    1. TEMPORAL creates Activity (activity_type: meeting) from
       DesignReview requirements (reviewers, duration, constraints).
    2. Query multi-resource Availability for all reviewers.
    3. Apply Constraints (review must occur before design gate Milestone).
    4. Create Bookings for reviewers and review room.
    5. Emit `substrate.temporal.booking.confirmed`.
    6. DESIGN transitions DesignReview (TERM-D022) to `scheduled`.
  Output:     Scheduled design review with temporal allocation.

FLOW-T008: SLA Breach Detection Flow (Cross-Substrate)
  Trigger:    TemporalServiceMetric (ENT-T021) breach_detected = true.
  Steps:
    1. TEMPORAL detects temporal performance breach (e.g., P95 response
       time exceeds threshold).
    2. Emit `substrate.temporal.service_metric.breached` with metric_id,
       breach details, current performance.
    3. GOVERNANCE consumes event.
    4. GOVERNANCE evaluates against Obligation (TERM-G005) whose
       action_required references this TemporalServiceMetric.
    5. If Obligation violated: GOVERNANCE creates Violation (TERM-G020).
    6. GOVERNANCE processes through Violation → Sanction lifecycle.
  Output:     TEMPORAL measurement + GOVERNANCE contractual enforcement.
```

---

## 8. INTEGRATION CONTRACTS (HOW SUBSTRATES CONNECT)

> Integration contract identifiers use INT-T prefix. Each contract
> defines the protocol between TEMPORAL and a peer substrate, including
> event schemas, delegation rules, and data exchange formats.

```
INT-T001: TEMPORAL ↔ BUSINESS Integration
  Purpose:    Coordinate temporal allocation with commercial operations.
  Protocol:
    — Event-driven via shared event mesh.
    — TEMPORAL emits: substrate.temporal.booking.confirmed,
      substrate.temporal.booking.cancelled,
      substrate.temporal.capacity.gap_detected,
      substrate.temporal.activity.completed.
    — BUSINESS emits: substrate.business.reservation.created (references
      Booking), substrate.business.order.created (demand signal),
      substrate.business.priority.changed.
  Delegation:
    — BUSINESS Reservation (TERM-023) references TEMPORAL Booking (TERM-T004)
      for temporal fields. Booking is authoritative for time/resource
      allocation. Reservation is authoritative for commercial terms.
    — BUSINESS Schedule trigger (TERM-017) recurring type delegates RFC 5545
      RRULE interpretation to TEMPORAL Recurrence (TERM-T005).
    — Project management composition: BUSINESS Entity (lifecycle) + TEMPORAL
      Schedule (temporal plan). Neither substrate alone constitutes project
      management.
  Name collision: BUSINESS TERM-017 "Schedule" = time-based trigger.
                  TEMPORAL TERM-T010 "Schedule" = constraint-satisfaction result.
                  Disambiguated in CROSS-SUBSTRATE-CONVENTIONS §7.

INT-T002: TEMPORAL ↔ COMPUTE Integration
  Purpose:    Execute scheduling solvers via COMPUTE Pipelines.
  Protocol:
    — TEMPORAL submits SchedulingProblem as COMPUTE Dataset input.
    — COMPUTE allocates Resources, runs solver Pipeline.
    — COMPUTE returns SchedulingSolution as Result.
  Schemas:
    SchedulingProblem: {
      activities[] (id, duration, priority, resource_requirements[]),
      dependencies[] (predecessor, successor, type, lag),
      constraints[] (type, participants, hardness, violation_penalty,
        relaxation_priority),
      resources[] (id, availability_windows[], capacity, skills[],
        transition_times[]),
      policies[] (type, parameters),
      objectives[] (metric, direction, weight)
    }
    SchedulingSolution: {
      assignments[] (activity_id, timewindow, resource_id),
      objective_values[] (objective_id, score),
      optimality_gap (numeric — distance from proven optimal, null if unknown),
      computation_time (duration),
      constraints_relaxed[] (constraint_id, relaxation_amount),
      infeasibility_explanations[] (if unsolvable: which constraints conflict)
    }
  Delegation Table (COMPUTE TERM-C007 Schedule types):
    one_shot        → TEMPORAL TimeWindow (TERM-T002) for temporal logic
    recurring       → TEMPORAL Recurrence (TERM-T005) for RRULE
    event_triggered → COMPUTE-owned (compute-state triggers)
    continuous      → COMPUTE-owned (always-running processes)
    conditional     → split: temporal predicates → TEMPORAL;
                      compute-state predicates → COMPUTE
  Solver pluggability: Multiple solvers registered (CP-SAT, OR-Tools, Gurobi,
    custom heuristics). TEMPORAL selects per SchedulingPolicy. COMPUTE
    treats each as a Pipeline implementation.

INT-T003: TEMPORAL ↔ PHYSICAL Integration
  Purpose:    Synchronize equipment state with scheduling availability.
  Protocol:
    — PHYSICAL emits: substrate.physical.asset.state_changed,
      substrate.physical.asset.degraded,
      substrate.physical.maintenance.completed.
    — TEMPORAL emits: substrate.temporal.booking.confirmed (for maintenance),
      substrate.temporal.activity.completed (maintenance done).
  State Mapping (PHYSICAL PhysicalAsset state → TEMPORAL Availability):
    Operational      → Available (full capacity)
    Degraded         → Conditionally Available (reduced capacity_level)
    LockedOut        → Unavailable (Bookings blocked, existing → Disruption)
    Shutdown         → Unavailable (permanent for shutdown duration)
    Decommissioned   → Unavailable (permanent, resource status → decommissioned)
  Boundary:   Purpose, not duration. PHYSICAL owns control loops, safety functions,
              equipment operation. TEMPORAL owns planning, coordination, resource
              allocation. A 200ms booking confirmation is TEMPORAL. A 200ms safety
              interlock is PHYSICAL. A 30-year maintenance plan is TEMPORAL. A 30-year
              monitoring system is PHYSICAL.
  Mirror:     INT-P008 in SUBSTRATE-PHYSICAL.

INT-T004: TEMPORAL ↔ GOVERNANCE Integration
  Purpose:    Enforce labor law and compliance constraints on scheduling.
  Protocol:
    — GOVERNANCE provides: Norms with structured temporal_constraint_spec
      ({constraint_type, duration, window, scope}). Example:
      {constraint_type: "minimum_rest", duration: "PT11H", window: "PT24H",
      scope: "per_worker"} for EU Working Time Directive.
    — TEMPORAL consumes as SchedulingPolicy compliance-type constraints.
    — TEMPORAL emits: substrate.temporal.scheduling_policy.violated,
      substrate.temporal.service_metric.breached.
    — GOVERNANCE processes through: Violation assessment → Sanction lifecycle.
  Enforcement split:
    Proactive:   TEMPORAL enforces during schedule creation (reject infeasible).
    Retroactive: GOVERNANCE enforces via ComplianceAssessment.
  SLA split:
    TEMPORAL: TemporalServiceMetric (TERM-T021) = temporal measurement.
    GOVERNANCE: Obligation (TERM-G005) = contractual obligation.
    GOVERNANCE: Sanction = consequence of breach.
  Envelope chain: Epistemic → TemporalEnvelope → Design. Temporal authority is
    resource-allocation between reasoning permission and physical commitment.
  Mirror:     INT-G008 in SUBSTRATE-GOVERNANCE.

INT-T005: TEMPORAL ↔ COMMUNICATION Integration
  Purpose:    Coordinate meeting scheduling with discourse and deadline tracking.
  Protocol:
    — TEMPORAL emits: substrate.temporal.booking.confirmed (meeting scheduled),
      substrate.temporal.deadline.approaching,
      substrate.temporal.deadline.breached.
    — COMMUNICATION emits: substrate.communication.participant.declined
      (decline speech act → TEMPORAL Disruption),
      substrate.communication.commitment.created (may trigger TEMPORAL Deadline).
  Meeting protocol: TEMPORAL resolves Availability and creates Bookings.
    On confirmation, COMMUNICATION creates Discourse instance.
  Deadline protocol: TEMPORAL is authoritative deadline tracker. COMMUNICATION
    Commitment.deadline may create TEMPORAL Deadline with source_ref. Single
    enforcement point; event-driven propagation.

INT-T006: TEMPORAL ↔ KNOWLEDGE Integration
  Purpose:    Exchange duration estimates and scheduling pattern data.
  Protocol:
    — KNOWLEDGE provides: Propositions (TERM-K001) for duration estimates,
      demand forecasts, and no-show probability models.
    — TEMPORAL consumes as planning parameters (Activity duration estimates,
      Capacity demand forecasts, overbooking probability models).
    — TEMPORAL emits: substrate.temporal.activity.completed (with actual
      duration) for KNOWLEDGE to update duration distribution models.
  v1.1 stochastic support: Activity.knowledge_proposition_ref enables
    full probability distribution integration.

INT-T007: TEMPORAL ↔ DESIGN Integration
  Purpose:    Schedule design reviews and generate production schedules from BOMs.
  Protocol:
    — DESIGN emits: substrate.design.review.scheduling_requested,
      substrate.design.bom.updated,
      substrate.design.fabrication_method.updated.
    — TEMPORAL emits: substrate.temporal.booking.confirmed (review scheduled),
      substrate.temporal.schedule.created (production schedule).
  Design review: DESIGN DesignReview → TEMPORAL Activity (meeting type).
  Production scheduling: DESIGN BOM (TERM-D021) + FabricationMethod (TERM-D020)
    → TEMPORAL Activities + Dependencies + ResourceRequirements → solver →
    production Schedule. See FLOW-T006.
  Mirror:     INT-D008 in SUBSTRATE-DESIGN.

INT-T008: TEMPORAL ↔ SPATIAL Integration
  Purpose:    Resolve travel durations for TransitionTime computation.
  Protocol:
    — TEMPORAL emits: substrate.temporal.travel_duration.requested
      Payload (RoutingProblem schema):
        {origin: {latitude, longitude} or address_text,
         destination: {latitude, longitude} or address_text,
         waypoints: [{latitude, longitude}],
         network_ref: nullable SpatialNetwork ref,
         vehicle_profile: nullable {height_m, width_m, length_m,
           weight_kg, axle_count, fuel_type, hazmat_class},
         avoid_features: [{feature_type, geometry}],
         time_of_departure: datetime,
         optimization_criterion: enum (fastest default)}
    — SPATIAL computes Route via FLOW-S003.
    — SPATIAL emits: substrate.spatial.route.computed
      Payload (RoutingSolution schema):
        {route_id, total_distance_m, estimated_duration_s,
         segments: [{segment_id, length_m, travel_time_s}],
         alternatives: [{route_id, distance_m, duration_s}],
         accuracy_ref, computation_time_ms}
    — TEMPORAL consumes duration for TransitionTime (TERM-T029).
  Delegation: SPATIAL owns route computation. TEMPORAL owns scheduling
    decision based on computed duration.
  Boundary:   SLA: Route computation ≤1s for single origin-destination
    (RUNTIME-S003 Tier 2). Mirror: INT-S001 in SUBSTRATE-SPATIAL.
```

### Cross-Substrate Event Topics

```
All events emitted or consumed by TEMPORAL across integration contracts INT-T001–T008.

Events Emitted by TEMPORAL:
  substrate.temporal.booking.confirmed              — Booking created and time slot locked
  substrate.temporal.booking.cancelled               — Booking cancelled, slot released
  substrate.temporal.schedule.created                — Schedule produced by solver
  substrate.temporal.schedule.disrupted              — Schedule invalidated by external event
  substrate.temporal.conflict.detected               — Scheduling collision found
  substrate.temporal.conflict.resolved               — Conflict resolution applied
  substrate.temporal.disruption.recovered             — Schedule recovered after disruption
  substrate.temporal.service_metric.breached          — SLA threshold violated
  substrate.temporal.deadline.breached                — Deadline missed, escalation triggered
  substrate.temporal.scheduling_policy.violated       — Governance constraint violated
  substrate.temporal.activity.completed               — Activity finished execution
  substrate.temporal.deadline.approaching              — Deadline approaching threshold (INT-T005)
  substrate.temporal.capacity.gap_detected             — Insufficient resource capacity
  substrate.temporal.travel_duration.requested           — Route computation request to SPATIAL

Events Consumed by TEMPORAL:
  substrate.business.reservation.created              — Commercial reservation (INT-T001)
  substrate.business.order.created                    — Demand signal (INT-T001)
  substrate.business.priority.changed                 — Priority adjustment (INT-T001)
  substrate.compute.execution.completed               — Solver result ready (INT-T002)
  substrate.physical.asset.state_changed              — Equipment state change (INT-T003)
  substrate.physical.asset.degraded                   — Equipment degradation (INT-T003)
  substrate.physical.maintenance.completed            — Maintenance done (INT-T003)
  substrate.governance.norm.effective                  — Scheduling constraint active (INT-T004)
  substrate.communication.discourse.resolved          — Discourse closed (INT-T005)
  substrate.communication.commitment.fulfilled        — Commitment completed (INT-T005)
  substrate.communication.participant.declined        — Decline speech act → Disruption (INT-T005)
  substrate.communication.commitment.created          — May trigger Deadline creation (INT-T005)
  substrate.knowledge.proposition.confidence_changed  — Duration estimate update (INT-T006)
  substrate.design.review.scheduling_requested        — Design review needs slot (INT-T007)
  substrate.design.bom.updated                        — BOM changed (INT-T007)
  substrate.design.fabrication_method.updated          — Manufacturing method changed (INT-T007)
  substrate.spatial.route.computed                     — Route duration available (INT-T008)
```

---

## 9. AUTHORIZATION & ACCESS MODEL

> Resource identifiers use RES-T prefix. This section defines who may
> perform which operations on which TEMPORAL entities. Schedule data is
> personal data (ASM-T013) — access control is a privacy requirement,
> not an optional feature.

### 9.1 Resources

```
RES-T001: Calendar           — create, read, update, archive
RES-T002: TimeWindow         — create, read
RES-T003: Availability       — compute, read (per visibility_level)
RES-T004: Booking            — create, read, modify, cancel
RES-T005: Recurrence         — create, read, update
RES-T006: Constraint         — create, read, update, relax
RES-T007: Activity           — create, read, update, cancel, defer
RES-T008: Milestone          — create, read, update
RES-T009: Dependency         — create, read, delete
RES-T010: Schedule           — create, read, modify, freeze, unfreeze, archive
RES-T011: Timeline           — read (immutable — no write operations)
RES-T012: Horizon            — create, read, update
RES-T013: Disruption         — create, read, respond
RES-T014: Conflict           — read, resolve
RES-T015: Resolution         — create, read, approve, apply, reverse
RES-T016: SchedulableResource — create, read, update, decommission
RES-T017: ResourceRequirement — create, read, update
RES-T018: Shift              — create, read, update
RES-T019: Rotation           — create, read, update, rebalance
RES-T020: Deadline           — create, read, waive
RES-T021: TemporalServiceMetric — configure, read
RES-T022: Buffer             — create, read
RES-T023: Cadence            — create, read, update
RES-T024: SchedulingObjective — create, read, update
RES-T025: TemporalEnvelope   — create, read, modify, revoke
RES-T026: SchedulingPolicy   — create, read, update, suspend
RES-T027: CalendarSystem     — register, read
RES-T028: Capacity           — compute, read
RES-T029: TransitionTime     — create, read, update
RES-T030: Waitlist           — create, read, enroll, offer, withdraw
```

### 9.2 Permission Matrix (Actor × Resource)

```
Legend: C=create R=read U=update D=delete/cancel X=execute (compute/resolve/approve)
       ·=no access  v=visibility-restricted read

Actor              |Cal |TW  |Avl |Bkg |Rec |Cst |Act |Mls |Dep |Sch |Tln |
ACT-T001 Scheduler |R   |CR  |RX  |CRUD|CR  |CRU |CRUD|CRU |CRD |CRUX|R   |
ACT-T002 Steward   |CRUD|CR  |RX  |R   |CRU |CRU |R   |R   |R   |RU  |R   |
ACT-T003 AI Narrow |R   |CR  |RX  |CRD |R   |R   |CRD |R   |CR  |CRU |R   |
ACT-T004 AI General|R   |CR  |RX  |CRUD|CR  |CRU |CRUD|CRU |CRD |CRUX|R   |
ACT-T005 Internal  |R   |R   |vR  |vR  |·   |·   |vR  |vR  |·   |vR  |vR  |
ACT-T006 External  |·   |·   |·   |·   |·   |·   |·   |·   |·   |·   |·   |
ACT-T007 Auditor   |R   |R   |R   |R   |R   |R   |R   |R   |R   |R   |R   |
ACT-T008 Ext Part  |·   |·   |vR  |CR  |·   |·   |·   |·   |·   |·   |·   |

Actor              |Hor |Dis |Cnf |Res |SRs |RRq |Shf |Rot |Ddl |TSM |
ACT-T001 Scheduler |R   |CRX |RX  |CRX |R   |CRU |RU  |R   |CRU |R   |
ACT-T002 Steward   |CRU |R   |R   |R   |CRUD|R   |CRUD|CRUD|R   |CRU |
ACT-T003 AI Narrow |R   |CRX |RX  |CR  |R   |CR  |R   |R   |CR  |R   |
ACT-T004 AI General|R   |CRX |RX  |CRX |R   |CRU |RU  |RU  |CRU |R   |
ACT-T005 Internal  |·   |·   |·   |·   |vR  |·   |vR  |vR  |vR  |·   |
ACT-T006 External  |·   |·   |·   |·   |·   |·   |·   |·   |·   |·   |
ACT-T007 Auditor   |R   |R   |R   |R   |R   |R   |R   |R   |R   |R   |
ACT-T008 Ext Part  |·   |·   |·   |·   |·   |·   |·   |·   |·   |·   |

Actor              |Buf |Cad |SOb |TEn |SPo |CSy |Cap |TTm |Wlt |
ACT-T001 Scheduler |CR  |R   |R   |·   |R   |R   |RX  |R   |CRU |
ACT-T002 Steward   |R   |CRUD|CRUD|CRUD|CRUD|CRU |RX  |CRUD|CRU |
ACT-T003 AI Narrow |CR  |R   |R   |R   |R   |R   |RX  |R   |CRU |
ACT-T004 AI General|CR  |R   |R   |R   |R   |R   |RX  |R   |CRU |
ACT-T005 Internal  |·   |vR  |·   |·   |·   |·   |·   |·   |CR  |
ACT-T006 External  |·   |·   |·   |·   |·   |·   |·   |·   |·   |
ACT-T007 Auditor   |R   |R   |R   |R   |R   |R   |R   |R   |R   |
ACT-T008 Ext Part  |·   |·   |·   |·   |·   |·   |·   |·   |CR  |

Notes:
  v = visibility-restricted: ACT-T005 sees own schedule + busy/free of colleagues.
      ACT-T008 sees public availability slots only.
  AI agents (ACT-T003, ACT-T004) permissions further bounded by TemporalEnvelope.
  ACT-T006 (External System) access governed by integration contract, not permission matrix.
  ACT-T007 (Auditor) has read-only access to ALL entities including scheduling_rationale,
  fairness metrics, and constraint relaxation history. Cannot modify any entity.
```

### 9.3 Visibility Controls

```
VISIBILITY-T001: Availability Visibility Levels
  full_detail:  Shows what is booked, by whom, for what activity.
                Granted to: ACT-T001, ACT-T002, ACT-T003, ACT-T004 (within scope).
  busy_free:    Shows only occupied/open time slots. No activity details.
                Granted to: ACT-T005 (colleagues), cross-organization (TRUST-T004).
  slots_only:   Shows bookable time slots without context.
                Granted to: ACT-T008 (external participants).

VISIBILITY-T002: Schedule Visibility Levels
  full:         All Activities, Bookings, rationale, constraint details.
                Granted to: ACT-T001, ACT-T002, ACT-T003, ACT-T004, ACT-T007.
  participant:  Own Activities and Bookings only. Others' details hidden.
                Granted to: ACT-T005.
  none:         No schedule visibility.
                Applied to: ACT-T008.
```

---

## 10. SECURITY & PRIVACY MODEL

> Schedule data is personal data (ASM-T013). This section defines
> classification, threats, and abuse prevention.

### 10.1 Data Classification

```
CLASS-T001: Schedule Content — CONFIDENTIAL
            Activity descriptions, Booking details, scheduling rationale,
            resource assignments. Reveals what people are doing and when.

CLASS-T002: Availability Data — RESTRICTED
            busy_free is INTERNAL (available to authenticated internal users).
            full_detail is CONFIDENTIAL (restricted to scheduling authority).
            slots_only is PUBLIC (available to external participants).

CLASS-T003: Workforce Scheduling Data — CONFIDENTIAL + PII
            Shift assignments, rotation schedules, labor constraint data,
            preference declarations. Contains PII: work hours, availability
            patterns, health-related constraints (pregnancy accommodations,
            disability adjustments).

CLASS-T004: Fairness Metrics — CONFIDENTIAL
            Rotation equity data, bias audit results. Sensitive: could reveal
            discrimination patterns.

CLASS-T005: Timeline & Audit Data — CONFIDENTIAL + COMPLIANCE
            Immutable schedule history. Required for compliance. Retention
            7+ years. Tamper-evident (hash chains).

CLASS-T006: TemporalEnvelope Configuration — RESTRICTED
            AI agent authority bounds. Access limited to ACT-T002 and ACT-T007.
```

### 10.2 Threat Model

```
THREAT-T001: Schedule Inference Attack
             Threat:     Inferring sensitive information (medical appointments,
                         legal consultations, job interviews) from availability
                         patterns, even with busy_free visibility.
             Mitigation: Configurable granularity for busy_free (e.g., report
                         availability in 4-hour blocks, not exact windows).
                         Noise injection option for high-sensitivity schedules.

THREAT-T002: Double-Booking Exploit
             Threat:     Malicious actor creates conflicting Bookings to deny
                         resource availability to others.
             Mitigation: CONC-T001 (optimistic concurrency). Rate limiting on
                         Booking creation (ACT-T008). Booking requires
                         authentication and authorization.

THREAT-T003: AI Scheduling Bias
             Threat:     AI agent systematically assigns unfavorable schedules
                         to specific resource groups (bias in scheduling_rationale).
             Mitigation: Mandatory scheduling_rationale. Fairness metrics on
                         Rotations (ENT-T019). Auditor (ACT-T007) read access
                         to all rationale and metrics. ACT-T008 bias audit.

THREAT-T004: Schedule Data Exfiltration
             Threat:     Bulk extraction of schedule data reveals organizational
                         patterns, capacity, and strategic plans.
             Mitigation: Rate limiting on queries. Audit logging on bulk reads.
                         Cross-org queries limited to busy_free (TRUST-T004).

THREAT-T005: Envelope Bypass
             Threat:     AI agent exceeds TemporalEnvelope authority.
             Mitigation: Envelope validation on every AI scheduling operation
                         (CAP-T033). Violations logged and rejected. No
                         self-modification of Envelopes.

THREAT-T006: Timeline Tampering
             Threat:     Modification of historical Timeline snapshots to hide
                         scheduling decisions (audit evasion).
             Mitigation: Timeline immutability (ENT-T011). Hash chains for
                         tamper evidence. Append-only storage.
```

### 10.3 Abuse Prevention

```
ABUSE-T001: Booking Spam Prevention
            External participants (ACT-T008) are rate-limited on Booking
            requests. Maximum bookings per time period configurable per
            organization. CAPTCHA or identity verification for anonymous
            booking portals.

ABUSE-T002: Waitlist Gaming Prevention
            Waitlist position is computed from enrollment_timestamp and
            priority — not manipulable. Re-enrollment after withdrawal
            resets timestamp. Expired entries cannot be re-enrolled at
            original position.

ABUSE-T003: Preference Abuse Prevention
            preference_declarations with priority=hard_constraint require
            legal_basis reference. Without legal_basis, preferences are
            treated as preference-level (best-effort, not enforced).
            Prevents gaming via false constraint declarations.
```

---

## 11. BEHAVIORAL CONTRACTS (INVARIANTS, PRECONDITIONS, POSTCONDITIONS)

> Behavioral contracts specify what MUST always be true (INV), what
> MUST be true before an operation (PRE), what MUST be true after (POST),
> what MUST NEVER happen (FORBID), and how failures are handled (FAIL).

### 11.1 Invariants

```
INV-T001: No double-booking on single-capacity resources.
          For any SchedulableResource with capacity_level.total = 1,
          at most one confirmed Booking may exist for any given instant.
          Enforced by CONC-T001.

INV-T002: All hard Constraints satisfied in feasible Schedules.
          If Schedule.feasibility_status = feasible, every Constraint with
          hardness=hard referencing Activities in that Schedule MUST be
          satisfied. Violated only if feasibility_status=relaxed (with
          Resolution records) or infeasible.

INV-T003: Timeline immutability.
          Once created, a Timeline (ENT-T011) is never modified. Any
          detected modification is a system integrity violation.

INV-T004: Scheduling rationale completeness.
          Every Booking and every scheduled Activity MUST have non-empty
          scheduling_rationale. No scheduling decision without explanation.

INV-T005: Envelope authority bounds.
          An AI agent's scheduling operations MUST NOT exceed its
          TemporalEnvelope limits. Any operation exceeding envelope
          bounds MUST be rejected before execution.

INV-T006: Dependency acyclicity.
          The Dependency graph within any Schedule MUST be a directed
          acyclic graph (DAG). Cycles MUST be detected and reported
          as Conflicts.

INV-T007: Calendar system consistency.
          All internal timestamps are UTC. CalendarSystem provides
          interpretation only. No entity stores local time as its
          authoritative timestamp.

INV-T008: Availability computation correctness.
          Availability = Calendar working periods - existing Bookings -
          Constraint restrictions - TransitionTimes, adjusted for
          capacity levels. Any divergence is a computation error.

INV-T009: Fairness metric currency.
          Rotation fairness_metrics MUST be recomputed after every
          Shift assignment change. Stale fairness metrics are a
          compliance risk (ASM-T010).

INV-T010: Event sourcing completeness.
          Every state change on every TEMPORAL entity produces an
          immutable Event. Current state is derivable from the
          event stream. No silent state changes.

INV-T011: Disruption cascade completeness.
          Every Disruption MUST have cascade_analysis computed before
          response. Responding to a Disruption without understanding
          its cascade violates Property T7.

INV-T012: Cross-substrate reference validity.
          Every cross-substrate reference (BUSINESS Reservation,
          PHYSICAL PhysicalAsset, GOVERNANCE Norm, etc.) MUST point
          to a valid entity in the referenced substrate. Dangling
          references MUST be detected and surfaced.
```

### 11.2 Preconditions

```
PRE-T001: Booking creation requires verified Availability.
          Before creating a Booking, the system MUST verify that the
          target SchedulableResource has available capacity in the
          requested TimeWindow. Stale Availability (beyond cache_ttl)
          MUST be recomputed.

PRE-T002: Schedule submission requires complete problem specification.
          Before submitting a SchedulingProblem to solver, all Activities
          MUST have defined duration and ResourceRequirements. All
          Dependencies MUST form a DAG. All Constraints MUST reference
          valid participants.

PRE-T003: Constraint relaxation requires Resolution with authority.
          Before relaxing any Constraint (even soft), a Resolution
          (ENT-T015) MUST exist with valid authority and justification.
          Hard constraint relaxation MUST have human authority.

PRE-T004: AI operation requires valid TemporalEnvelope.
          Before any AI agent scheduling operation, the system MUST
          verify the agent has an active (not expired, not revoked)
          TemporalEnvelope covering the requested operation.

PRE-T005: Cross-org availability query requires consent.
          Before querying another organization's Availability, a valid
          GOVERNANCE ConsentRecord (TERM-G027) MUST exist authorizing
          the data exchange. Default: busy_free visibility only.

PRE-T006: Shift assignment requires labor constraint validation.
          Before assigning a Shift to a SchedulableResource, all
          labor_constraints on the Shift and all preference_declarations
          with priority=hard_constraint on the Resource MUST be validated.
```

### 11.3 Postconditions

```
POST-T001: After Booking confirmation, Availability is updated.
           After a Booking transitions to confirmed, the affected
           SchedulableResource's Availability cache MUST be invalidated
           and recomputed on next query.

POST-T002: After Schedule modification, Timeline is created.
           After any modification to an active Schedule (Activity added/
           removed, Booking changed, Constraint relaxed), a new Timeline
           snapshot MUST be created with delta_from_previous computed.

POST-T003: After Disruption detection, cascade analysis is computed.
           After a Disruption is created, cascade_analysis MUST be
           computed before any response action is taken.

POST-T004: After Conflict resolution, affected parties are notified.
           After a Resolution is applied, all affected participants
           (whose Bookings were modified) MUST be notified. Notification
           refs recorded in Resolution.

POST-T005: After service metric breach, event is emitted.
           After TemporalServiceMetric.breach_detected transitions to
           true, `substrate.temporal.service_metric.breached` MUST be
           emitted for GOVERNANCE consumption.

POST-T006: After Activity completion, actual duration is recorded.
           After an Activity transitions to completed, actual_start,
           actual_end, and actual_duration MUST be recorded.
           `substrate.temporal.activity.completed` MUST be emitted
           with actual duration for KNOWLEDGE consumption.
```

### 11.4 Forbidden Operations

```
FORBID-T001: AI agents MUST NOT relax hard Constraints without
             human approval. Hard constraint relaxation authority is
             exclusively human (ACT-T001, ACT-T002).

FORBID-T002: AI agents MUST NOT create or modify their own
             TemporalEnvelopes. Envelope management is exclusively
             human (ACT-T002).

FORBID-T003: No entity may modify a Timeline after creation.
             Timelines are append-only, immutable records.

FORBID-T004: No Booking may be created without scheduling_rationale.
             Empty or null scheduling_rationale is a system error.

FORBID-T005: No cross-org Availability query may return full_detail
             without explicit ConsentRecord authorization.
             Default is busy_free (TRUST-T004).

FORBID-T006: No Schedule may be marked feasible while hard Constraints
             are violated. feasibility_status=feasible requires all
             hard Constraints satisfied.

FORBID-T007: No Disruption response may proceed without cascade_analysis.
             Responding to a Disruption without cascade analysis risks
             creating secondary Disruptions.

FORBID-T008: No Shift assignment may violate legally-backed labor
             constraints. preference_declarations with
             priority=hard_constraint and legal_basis are not relaxable.

FORBID-T009: No scheduling operation may bypass TemporalEnvelope
             validation for AI agents. Every AI operation is checked.

FORBID-T010: No Waitlist position manipulation. Position is computed
             from ordering_policy (timestamp + priority), not settable.

FORBID-T011: No silent state changes. Every entity modification MUST
             produce an Event. Shadow updates are system integrity
             violations.

FORBID-T012: No retroactive Timeline modification. Historical schedule
             state is immutable. "What was the schedule on March 15?"
             returns the Timeline from that date, unmodified.
```

### 11.5 Failure Modes

```
FAIL-T001: Solver timeout.
           If COMPUTE solver exceeds time limit, return best-known
           feasible solution (if any) with optimality_bound=unknown.
           If no feasible solution found within time limit, return
           infeasible with partial explanation.

FAIL-T002: Availability computation failure.
           If Availability cannot be computed (missing Calendar data,
           unreachable PHYSICAL state), return availability_state=unknown
           with error details. Do NOT return stale Availability as
           current.

FAIL-T003: Cross-substrate event delivery failure.
           If an event (booking.confirmed, service_metric.breached)
           fails to deliver to the target substrate, retry with
           exponential backoff. After retry exhaustion, create an
           internal alert and log the undelivered event.

FAIL-T004: Cascade analysis timeout.
           If cascade_analysis for a Disruption exceeds computation
           limit (very large schedules), return partial cascade with
           depth_reached and estimated_total_impact. Do NOT skip
           cascade analysis — partial is acceptable, absent is not.

FAIL-T005: Conflict detection race condition.
           If two concurrent Booking requests pass Availability check
           but create a double-booking, the later-confirmed Booking
           is detected as a Conflict post-hoc. The Conflict is
           surfaced for Resolution. This is the optimistic concurrency
           model (CONC-T001).

FAIL-T006: Envelope validation failure.
           If TemporalEnvelope cannot be validated (envelope service
           unavailable), the AI scheduling operation MUST be rejected.
           Fail-closed, not fail-open. Human operations are not affected.

FAIL-T007: GOVERNANCE Norm consumption failure.
           If TEMPORAL cannot consume a GOVERNANCE Norm with
           temporal_constraint_spec (malformed spec, unknown constraint
           type), log the failure, alert ACT-T002, and do NOT create
           the corresponding SchedulingPolicy. Missing compliance
           constraints are surfaced, not silently ignored.

FAIL-T008: Timeline hash verification failure.
           If a Timeline's hash does not match its contents on read,
           this is a tamper detection. Alert immediately. The Timeline
           is marked as potentially compromised. Investigation required.
```

---

## 12. DECISION POINTS

> Decision point identifiers use DEC-T prefix. Each identifies a point
> where the system or a human must choose between alternatives with
> significant scheduling consequences.

```
DEC-T001: Conflict Resolution Strategy Selection
          When:       A Conflict (ENT-T014) is detected with severity ≥ major.
          Options:    reschedule (move activity), reassign (different resource),
                      split (break activity), defer (postpone), override (proceed
                      despite conflict), cancel, escalate, accept_conflict.
          Criteria:   Impact on Schedule quality_scores, number of affected
                      parties, reversibility, alignment with SchedulingPolicy.
          Authority:  Minor: AI agent within envelope. Major: ACT-T001.
                      Hard constraint relaxation: ACT-T001 or ACT-T002.
          Record:     Resolution (ENT-T015) with justification.

DEC-T002: Scheduling Horizon Selection
          When:       Creating a new Schedule or reconfiguring an existing one.
          Options:    operational (days/hours), tactical (weeks/days),
                      strategic (months/weeks).
          Criteria:   Schedule purpose, required precision, update frequency,
                      resource stability. ER schedule: operational. Annual
                      capacity plan: strategic.
          Authority:  ACT-T002 (Temporal Steward).
          Record:     Horizon (ENT-T012) configuration.

DEC-T003: Solver Selection
          When:       Submitting a SchedulingProblem to COMPUTE.
          Options:    CP-SAT (constraint programming), MILP (mixed-integer
                      linear programming), genetic algorithm, custom heuristic,
                      rule-based (simple assignment).
          Criteria:   Problem size, time budget, optimality requirement,
                      constraint complexity. Small problems: exact solver.
                      Large problems: heuristic with time limit.
          Authority:  SchedulingPolicy or ACT-T002 configuration.
          Record:     Schedule.solver_ref.

DEC-T004: Disruption Response Strategy
          When:       Disruption (ENT-T013) detected with severity ≥ minor.
          Options:    immediate auto-response, within-hour response, next-cycle
                      response, manual human response.
          Criteria:   Severity, domain (ER: immediate; construction: next-cycle),
                      SchedulingPolicy disruption_response configuration.
          Authority:  Per SchedulingPolicy. Escalation to ACT-T001 if auto-
                      response fails.
          Record:     Disruption status transitions per SM-T005.

DEC-T005: Constraint Relaxation Order
          When:       No feasible Schedule exists with all Constraints.
          Options:    Relax constraints in relaxation_priority order (lowest
                      first). Preference → soft → hard (hard requires human).
          Criteria:   violation_penalty (minimize total penalty cost),
                      relaxation_priority (respect priority ordering),
                      reversibility (prefer reversible relaxations).
          Authority:  Soft: AI agent within envelope. Hard: ACT-T001/T002.
          Record:     Resolution (ENT-T015) per relaxed Constraint.

DEC-T006: Overbooking Level
          When:       Configuring SchedulingPolicy for booking-heavy domains
                      (airlines, hotels, healthcare).
          Options:    No overbooking (0%), conservative (1-3%), moderate
                      (4-8%), aggressive (9-15%).
          Criteria:   Historical no-show rate, cost of denial vs. overflow,
                      customer experience impact, regulatory constraints.
          Authority:  ACT-T002 (Temporal Steward).
          Record:     SchedulingPolicy (overbooking type) with rate and model.
```

---

## 13. CONCURRENCY & ORDERING

> Concurrency identifiers use CONC-T prefix. Scheduling is inherently
> concurrent: multiple actors create Bookings simultaneously on shared
> resources.

```
CONC-T001: Double-Booking Prevention
           Model:     Optimistic concurrency with conflict detection on
                      resource-timewindow pairs.
           Mechanism: Each Booking creation checks Availability at request
                      time. On confirmation, the system verifies no concurrent
                      Booking was confirmed for the same resource-timewindow
                      pair. If collision detected: later-confirmed Booking
                      is flagged as Conflict (double_booking type).
           Trade-off: Optimistic concurrency allows higher throughput than
                      pessimistic locking. Rare conflicts (< 0.1% of bookings)
                      are resolved post-hoc. For high-contention resources,
                      implementations MAY use pessimistic locking.
           Scope:     Per SchedulableResource, per TimeWindow overlap.

CONC-T002: Schedule Version Ordering
           Model:     Monotonically increasing version numbers per Schedule.
           Mechanism: Every Schedule modification increments version. Timeline
                      snapshots carry the version. Concurrent modifications
                      are serialized by version number. Stale-version
                      modifications are rejected (optimistic locking).

CONC-T003: Event Ordering
           Model:     Causal ordering within entity scope. Global ordering
                      via event timestamp + trace_id.
           Mechanism: Events for the same entity are causally ordered (each
                      event references the prior event for that entity).
                      Cross-entity events are timestamp-ordered with
                      eventual consistency.

CONC-T004: Availability Cache Consistency
           Model:     Eventually consistent with bounded staleness.
           Mechanism: Availability caches are invalidated on Booking
                      confirmation/cancellation. cache_ttl bounds maximum
                      staleness. Critical operations (Booking creation)
                      force re-computation if cache age > threshold.

CONC-T005: Cross-Substrate Event Ordering
           Model:     At-least-once delivery with idempotent consumers.
           Mechanism: Events emitted to the cross-substrate event mesh
                      (CROSS-SUBSTRATE-CONVENTIONS §3) are delivered
                      at-least-once. Consumers MUST be idempotent.
                      Duplicate detection via event_id.
```

---

## 14. ERROR HANDLING & RECOVERY

> Error identifiers use ERR-T prefix.

```
ERR-T001: Invalid TimeWindow (start ≥ end) → reject with validation error.
ERR-T002: Dependency cycle detected → create Conflict (dependency_cycle), reject.
ERR-T003: Resource not found → return not_found error with resource_id.
ERR-T004: Availability computation timeout → return partial result with warning.
ERR-T005: Solver timeout → return best-known solution or infeasible (FAIL-T001).
ERR-T006: Constraint violation on Booking → create Conflict, return violation details.
ERR-T007: TemporalEnvelope exceeded → reject operation, log violation (FAIL-T006).
ERR-T008: Calendar inheritance cycle → reject, return cycle path.
ERR-T009: Recurrence rule parse error → reject with syntax error details.
ERR-T010: Cross-substrate reference invalid → log warning, mark as dangling.
ERR-T011: Booking hold expired → release slot, notify requestor, offer to Waitlist.
ERR-T012: Schedule version conflict → reject stale modification, return current version.
ERR-T013: Capacity computation overflow → partition into sub-pools, compute separately.
ERR-T014: TransitionTime lookup miss → use default (typical_duration), log warning.
ERR-T015: Waitlist full (max_size reached) → reject enrollment, return queue position info.
ERR-T016: Service metric computation error → mark metric as unavailable, alert ACT-T002.
ERR-T017: Policy configuration error → reject policy, return validation errors.
ERR-T018: Timeline hash mismatch → alert system integrity violation (FAIL-T008).
```

---

## 15. PERSISTENCE REQUIREMENTS

> Persistence identifiers use PERS-T prefix.

```
PERS-T001: Event Store
           All TEMPORAL Events are persisted in an append-only event store.
           Events are immutable. No deletion. No modification.
           Retention: minimum 7 years for compliance-relevant schedules
           (matching GOVERNANCE). Domain-specific extensions: healthcare
           schedules 10 years, safety-related schedules 30 years.
           Configurable per SchedulingPolicy.

PERS-T002: Timeline Archive
           All Timeline snapshots are persisted immutably with integrity
           hashes. Timelines are never deleted. Archived Timelines may be
           moved to cold storage after configurable period but MUST remain
           queryable for retroactive analysis.

PERS-T003: Active State Store
           Current state of all active entities (Schedules, Bookings,
           Activities, Resources) is derived from the event stream and
           maintained in a queryable store. This is a cache of the event
           stream, not the authoritative record.

PERS-T004: Availability Cache
           Computed Availability is cached with configurable TTL per
           resource. Cache is invalidated on Booking confirmation/
           cancellation. Cache is re-computable from authoritative
           data (Calendar, Bookings, Constraints).
```

---

## 16. MIGRATION & ONBOARDING

> Onboarding identifiers use ONBOARD-T prefix. Each describes a path
> for importing existing scheduling data into TEMPORAL.

```
ONBOARD-T001: iCalendar Import (RFC 5545)
              Source:   .ics files, CalDAV servers, Google Calendar, Outlook.
              Maps to:  Calendar → ENT-T001, VEVENT → ENT-T007 (Activity) +
                        ENT-T004 (Booking), RRULE → ENT-T005 (Recurrence),
                        VTODO → ENT-T007 (Activity, task type),
                        VFREEBUSY → ENT-T003 (Availability).
              Notes:    VTIMEZONE → CalendarSystem reference. Attendee status
                        → Booking status. VALARM → Deadline notification_triggers.

ONBOARD-T002: MS Project / MPP Import
              Source:   .mpp files, Project Server, Project Online.
              Maps to:  Task → ENT-T007 (Activity), Milestone → ENT-T008,
                        Link → ENT-T009 (Dependency, type FS/SS/FF/SF),
                        Resource → ENT-T016 (SchedulableResource),
                        Assignment → ENT-T004 (Booking), Calendar → ENT-T001,
                        Baseline → ENT-T011 (Timeline snapshot).
              Notes:    Duration types (fixed/effort/resource-driven) →
                        Activity duration.type. Lag → Dependency.lag.

ONBOARD-T003: Workforce Platform Import (Kronos/UKG, Deputy, etc.)
              Source:   Workforce management APIs, shift export files.
              Maps to:  Shift pattern → ENT-T018, Employee → ENT-T016
                        (SchedulableResource, person type), Shift assignment →
                        ENT-T004 (Booking), Schedule → ENT-T010 (workforce type),
                        Time-off → Calendar exception (unavailable).
              Notes:    Labor rules → SchedulingPolicy (compliance type) with
                        GOVERNANCE Norm references for legal backing.

ONBOARD-T004: CMMS Import (Maximo, SAP PM)
              Source:   Maintenance management system APIs/exports.
              Maps to:  Work order → ENT-T007 (Activity, maintenance type),
                        Equipment → ENT-T016 (SchedulableResource, equipment type)
                        with physical_asset_ref → PHYSICAL,
                        PM schedule → ENT-T005 (Recurrence) + ENT-T010 (Schedule,
                        maintenance type), Crew → ENT-T016 pool.
              Notes:    Preventive maintenance intervals → Recurrence rules.

ONBOARD-T005: Cron/Airflow Import
              Source:   crontab files, Airflow DAG definitions.
              Maps to:  Cron expression → ENT-T005 (Recurrence),
                        Scheduled job → ENT-T007 (Activity) + COMPUTE Pipeline
                        reference. Airflow schedule_interval → Recurrence.
                        Airflow DAG → COMPUTE Pipeline (per INT-T002).
              Notes:    Per INT-T002: TEMPORAL owns "when" (Recurrence).
                        COMPUTE owns "what" and "how" (Pipeline).

ONBOARD-T006: Custom CSV/API Import
              Source:   Spreadsheet schedules, custom booking databases.
              Maps to:  Row → ENT-T007 (Activity) or ENT-T004 (Booking)
                        depending on content. Date/time columns → TimeWindow
                        with CalendarSystem reference for timezone interpretation.
              Notes:    Requires mapping configuration per source schema.
                        Validation: duplicate detection, constraint checking
                        on import.
```

---

## 17. OPERATIONAL PROFILE

> Operational identifiers use OPS-T prefix.

```
OPS-T001: Throughput Profile
          Peak:       20 billion temporal events/day globally (ASM-T009).
          Typical:    5-8 billion events/day.
          Burst:      10x peak for 15-minute windows (Monday morning
                      scheduling surge, shift change peaks).
          Booking:    Average 2KB payload (ASM-T008).
          Schedule:   Average 64KB payload. Max 10MB for complex production
                      schedules (Content Store reference for overflow).

OPS-T002: Latency Profile
          Booking confirmation:    Target P99 < 500ms (implementation-dependent).
          Availability query:      Target P95 < 200ms (cached),
                                   P95 < 2s (computed).
          Schedule generation:     Seconds to hours depending on problem size
                                   and solver. Not latency-bounded — quality-
                                   bounded by SchedulingObjective targets.
          Disruption cascade:      Target P95 < 5s for cascade_analysis.
          Cross-substrate event:   Target P99 < 1s delivery.

OPS-T003: Availability Profile
          System availability:     99.9% (3 nines) for Booking and Availability
                                   operations. Lower target acceptable for
                                   Schedule generation (batch-tolerant).
          Degraded mode:           If solver unavailable: manual scheduling via
                                   direct Booking creation (bypass solver).
                                   If cross-substrate events delayed: local
                                   operations continue; integration state
                                   reconciled on reconnect.
```

---

## 18. TEST PLAN

> Test identifiers use TEST-T prefix.

```
TEST-T001: Create Calendar with working periods and verify inheritance.
TEST-T002: Create TimeWindow and verify half-open interval semantics.
TEST-T003: Compute Availability for single-capacity resource with existing Bookings.
TEST-T004: Compute Availability for multi-capacity resource (partial availability).
TEST-T005: Create Recurrence with complex RRULE and verify instance generation.
TEST-T006: Verify Recurrence across DST transitions.
TEST-T007: Register CalendarSystem (non-Gregorian) and verify date interpretation.
TEST-T008: Create Activity with PERT three-point duration estimate.
TEST-T009: Create Dependencies (all four types: FS, SS, FF, SF) with lag/lead.
TEST-T010: Detect dependency cycle and report as Conflict.
TEST-T011: Create Constraint with hardness levels and verify solver behavior.
TEST-T012: Verify constraint relaxation order (preference → soft) with Resolution records.
TEST-T013: Verify hard constraint infeasibility blocks Schedule creation.
TEST-T014: Create Deadline with notification triggers and verify escalation.
TEST-T015: Create Schedule via solver and verify feasibility_status.
TEST-T016: Verify Timeline snapshot creation on Schedule modification.
TEST-T017: Compare two Timelines and verify delta computation.
TEST-T018: Verify critical path and slack computation in Timeline.
TEST-T019: Create Booking and verify double-booking prevention (CONC-T001).
TEST-T020: Verify Booking hold expiry auto-releases slot.
TEST-T021: Create multi-resource Booking (all_simultaneous synchronization).
TEST-T022: Verify TransitionTime enforcement between consecutive Bookings.
TEST-T023: Create Shift with labor constraints and verify assignment validation.
TEST-T024: Create Rotation and verify fairness_metrics computation.
TEST-T025: Verify Rotation rebalancing when equity threshold exceeded.
TEST-T026: Create Cadence and verify boundary action Activity generation.
TEST-T027: Detect double-booking Conflict and verify lifecycle (SM-T004).
TEST-T028: Propose and apply Resolution with justification.
TEST-T029: Create Disruption and verify cascade_analysis computation.
TEST-T030: Verify disruption-triggered rescheduling flow (FLOW-T003).
TEST-T031: Compute Capacity and verify gap_analysis.
TEST-T032: Create Waitlist, enroll entries, verify slot offer on Booking cancellation.
TEST-T033: Verify SchedulingObjective multi-objective optimization quality_scores.
TEST-T034: Configure TemporalServiceMetric and verify breach detection + event emission.
TEST-T035: Verify SchedulingPolicy compliance-type constraint from GOVERNANCE Norm.
TEST-T036: Verify TemporalEnvelope enforcement (reject operation exceeding envelope).
TEST-T037: Meeting scheduling flow (FLOW-T004) with participant decline → Disruption.
TEST-T038: Maintenance scheduling flow (FLOW-T005) with PHYSICAL state change.
TEST-T039: Production schedule generation flow (FLOW-T006) with DESIGN BOM input.
TEST-T040: SLA breach detection flow (FLOW-T008) with GOVERNANCE Obligation reference.
```

---

## 19. OBSERVABILITY & AUDITABILITY

### 19.1 Logging

```
LOG-T001: All Booking create/modify/cancel operations logged with actor, timestamp,
          scheduling_rationale, and affected entities.
LOG-T002: All Schedule create/modify operations logged with version, solver_ref,
          feasibility_status, and quality_scores.
LOG-T003: All Conflict detect/resolve operations logged with conflict_type,
          severity, resolution_type, authority, and justification.
LOG-T004: All Disruption detect/respond/recover operations logged with
          disruption_type, cascade_analysis, and resolution timeline.
LOG-T005: All TemporalEnvelope validation operations logged (both pass and reject).
LOG-T006: All Constraint relaxation operations logged with authority and justification.
LOG-T007: All cross-substrate event emissions and consumptions logged with trace_id.
LOG-T008: All Availability computation operations logged with inputs and cache status.
LOG-T009: All SchedulingPolicy violation detections logged with policy_id and action taken.
```

### 19.2 Metrics

```
MET-T001: Booking confirmation latency (P50, P95, P99).
MET-T002: Availability query latency (P50, P95, P99, cached vs computed).
MET-T003: Schedule generation time by problem size and solver type.
MET-T004: Conflict detection rate per resource pool and time period.
MET-T005: Conflict resolution time (detection to resolution).
MET-T006: Disruption frequency per schedule type and time period.
MET-T007: Disruption cascade depth distribution.
MET-T008: Schedule revision frequency (proxy for schedule stability).
MET-T009: Fairness metric values per Rotation.
MET-T010: Buffer consumption rates per Schedule.
MET-T011: Capacity utilization per resource pool.
MET-T012: Waitlist conversion rate (enrollment to Booking).
MET-T013: SchedulingPolicy violation rate per policy type.
MET-T014: TemporalEnvelope rejection rate per agent.
```

### 19.3 Alerts

```
ALERT-T001: Double-booking detected (despite CONC-T001 prevention).
ALERT-T002: Hard constraint infeasibility in Schedule generation.
ALERT-T003: TemporalServiceMetric breach detected.
ALERT-T004: TemporalEnvelope violation by AI agent.
ALERT-T005: Timeline hash mismatch (tamper detection).
ALERT-T006: Disruption cascade depth exceeds configurable threshold.
ALERT-T007: Capacity gap detected in critical resource pool.
ALERT-T008: Fairness metric exceeds equity threshold in Rotation.
ALERT-T009: Cross-substrate event delivery failure after retry exhaustion.
ALERT-T010: Solver repeatedly returning infeasible for previously feasible Schedules.
```

---

## 20. DEFINITION OF DONE

```
DONE-T001: All 30 primitives (TERM-T001 through TERM-T030) have corresponding
           entity definitions (ENT-T), state machines where applicable (SM-T001
           through SM-T005), and interface operations (IFC-T).

DONE-T002: All 34 capabilities (CAP-T001 through CAP-T034) are testable via
           the 40 test cases (TEST-T001 through TEST-T040).

DONE-T003: All 8 integration contracts (INT-T001 through INT-T008) have defined
           event schemas, delegation rules, and protocol specifications.

DONE-T004: All 5 state machines (SM-T001 through SM-T005) have complete state/
           transition/guard specifications with no unreachable states and no
           missing transitions.

DONE-T005: All 12 invariants (INV-T001 through INV-T012) are verifiable at
           runtime. Each has at least one test case exercising the invariant.

DONE-T006: All 12 forbidden operations (FORBID-T001 through FORBID-T012) have
           corresponding enforcement mechanisms and test cases verifying
           rejection behavior.

DONE-T007: All 8 data flows (FLOW-T001 through FLOW-T008) are end-to-end
           testable, including the 4 cross-substrate flows.

DONE-T008: The permission matrix (Section 9.2) is implemented and verified for
           all 8 actors across all 30 resources.

DONE-T009: TemporalEnvelope enforcement is verified: AI agents with no envelope
           have zero scheduling authority, and envelope constraints are enforced
           on every AI operation.

DONE-T010: The specification is implementable as a protocol (ASM-T007): no
           implementation-specific assumptions, no vendor lock-in, all
           interfaces use standard schemas.
```

---

## 21. OPEN QUESTIONS & RISKS

```
OQ-T001: Should speculative/what-if scheduling be a first-class operation?
         Risk:       Without preview, schedule changes commit without impact analysis.
         Mitigation: Schedule clone + Timeline compare as composition pattern in v1.
                     Dedicated what-if interface possible in v1.1.
         Status:     Design decision — composition pattern in v1.

OQ-T002: What is the exact interface between TEMPORAL constraint model and
         COMPUTE solver execution?
         Risk:       Tight coupling reduces solver pluggability.
         Resolution: Defined in INT-T002 with SchedulingProblem/SchedulingSolution schemas.
         Status:     Resolved (directional).

OQ-T003: How to schedule across trust boundaries (inter-organization)?
         Risk:       Organizations won't share full availability.
         Mitigation: Availability supports busy/free granularity (VISIBILITY-T001).
                     GOVERNANCE ConsentRecord governs data sharing.
         Status:     Deferred to implementation experience.

OQ-T004: Should overbooking be a primitive or SchedulingPolicy?
         Risk:       If primitive, complicates core model; if policy, inconsistent support.
         Resolution: SchedulingPolicy approach with overbooking type.
         Status:     Resolved.

OQ-T005: How to represent duration uncertainty (ranges vs distributions)?
         Risk:       Ranges imprecise; distributions complex.
         Resolution: v1 uses PERT three-point (min/expected/max). Full distributions
                     via KNOWLEDGE Confidence deferred to v1.1.
         Status:     Deferred.

OQ-T006: Schedule history retention period?
         Risk:       Unbounded = storage/privacy concern; insufficient = no analysis/compliance.
         Resolution: Configurable per SchedulingPolicy. Default 7+ years for compliance.
                     Event sourcing enables selective pruning while preserving audit trail.
         Status:     Design decision.

OQ-T007: Should "soft" resources (attention, energy, cognitive load) be schedulable?
         Risk:       Ignoring produces unsustainable schedules (back-to-back meetings).
         Mitigation: SchedulableResource can model as depleting/replenishing resource.
                     Buffer (time_between type) addresses the most common case.
                     Full support deferred to v1.1.
         Status:     Deferred.

OQ-T008: Does TEMPORAL need a dedicated temporal pattern query language?
         Risk:       Ad-hoc temporal queries are complex (Allen's interval algebra).
         Mitigation: v1 provides standard query interfaces (IFC-T). Allen's 13 temporal
                     relations as theoretical foundation. DSL deferred to implementation.
         Status:     Deferred.
```

---

## 22. IMPLEMENTATION NOTES

### 22.1 Recommended Build Phases

```
Phase 1: Core Temporal Model
         Calendar, TimeWindow, Availability, Recurrence, CalendarSystem.
         Basic Booking creation with double-booking prevention.
         Single-resource scheduling only.

Phase 2: Activity & Constraint Model
         Activity, Milestone, Dependency, Constraint, Deadline.
         Schedule creation with solver integration (INT-T002).
         Timeline snapshots. Critical path computation.

Phase 3: Resource & Workforce
         SchedulableResource with capacity, skills, preferences.
         ResourceRequirement with multi-resource synchronization.
         Shift, Rotation, Cadence. Fairness metrics.

Phase 4: Disruption & Optimization
         Disruption detection and cascade analysis.
         Conflict detection and Resolution lifecycle.
         Buffer management. Capacity planning.
         SchedulingObjective and multi-objective optimization.
         TransitionTime. Waitlist.

Phase 5: Integration & Governance
         All 8 cross-substrate integration contracts.
         TemporalEnvelope enforcement.
         SchedulingPolicy (all types including compliance).
         TemporalServiceMetric with GOVERNANCE integration.
         Full audit trail and observability.
```

### 22.2 Composition Patterns

```
PATTERN-T001: Project Management
              BUSINESS Entity (project lifecycle: initiated → planning →
              executing → completed) + TEMPORAL Schedule (temporal plan with
              Activities, Dependencies, Milestones, Bookings).
              Neither substrate alone constitutes project management.
              BUSINESS owns "what" and "why." TEMPORAL owns "when" and "who."

PATTERN-T002: Production Scheduling
              DESIGN BOM + FabricationMethod → TEMPORAL Activities +
              Dependencies + ResourceRequirements → COMPUTE solver →
              TEMPORAL Schedule → BUSINESS demand fulfillment.
              See FLOW-T006 for detailed flow.

PATTERN-T003: Meeting Scheduling
              TEMPORAL (find available time, create Bookings) +
              COMMUNICATION (create Discourse for meeting content).
              See FLOW-T004 for detailed flow.

PATTERN-T004: Maintenance Scheduling
              PHYSICAL (equipment state, calibration needs) +
              TEMPORAL (schedule maintenance activities) +
              BUSINESS (maintenance cost tracking).
              See FLOW-T005 for detailed flow.

PATTERN-T005: SLA Management
              TEMPORAL (measure temporal performance via TemporalServiceMetric) +
              GOVERNANCE (contractual obligation via Obligation, consequence
              via Sanction). See FLOW-T008 for detailed flow.
```

---

## 23. COMPLETENESS CHECKLIST

```
Section                          | Artifacts              | Count | Status
---------------------------------|------------------------|-------|--------
Preamble                         | ASI-1 voice            | 1     | ✓
0. Sources, Assumptions, Unknowns| SRC-T, ASM-T, UNK-T   |16,13,8| ✓
1. System Intent                 | ACT-T, NG-T, SUCCESS,  |       |
                                 | FAILURE                |8,7,5,5| ✓
2. System Boundaries             | DEP-T, EXCL-T, TRUST-T,|       |
                                 | NETWORK-T, RUNTIME-T   |9,6,5,3,3| ✓
3. Glossary                      | TERM-T                 | 30    | ✓
4. Core Capabilities             | CAP-T                  | 34    | ✓
5. Domain Objects & State        | ENT-T, SM-T            | 30, 5 | ✓
6. Interfaces                    | IFC-T                  | 10    | ✓
7. Data Flows                    | FLOW-T                 | 8     | ✓
8. Integration Contracts         | INT-T                  | 8     | ✓
9. Authorization & Access        | RES-T, VISIBILITY-T    | 30, 2 | ✓
10. Security & Privacy           | CLASS-T, THREAT-T,     |       |
                                 | ABUSE-T                |6, 6, 3| ✓
11. Behavioral Contracts         | INV-T, PRE-T, POST-T, |       |
                                 | FORBID-T, FAIL-T       |12,6,6,12,8| ✓
12. Decision Points              | DEC-T                  | 6     | ✓
13. Concurrency & Ordering       | CONC-T                 | 5     | ✓
14. Error Handling               | ERR-T                  | 18    | ✓
15. Persistence                  | PERS-T                 | 4     | ✓
16. Migration & Onboarding       | ONBOARD-T              | 6     | ✓
17. Operational Profile          | OPS-T                  | 3     | ✓
18. Test Plan                    | TEST-T                 | 40    | ✓
19. Observability                | LOG-T, MET-T, ALERT-T  |9,14,10| ✓
20. Definition of Done           | DONE-T                 | 10    | ✓
21. Open Questions               | OQ-T                   | 8     | ✓
22. Implementation Notes         | Phase, PATTERN-T       | 5, 5  | ✓
23. Completeness Checklist       | This table             | 1     | ✓
24. Traceability Map             | Below                  | 1     | ✓
```

---

## 24. TRACEABILITY MAP

```
Source → Primitive → Capability → Entity → Interface → Test

SRC-T001 (Calendar) → TERM-T001 (Calendar), TERM-T002 (TimeWindow),
  TERM-T003 (Availability), TERM-T005 (Recurrence), TERM-T027 (CalendarSystem)
  → CAP-T001–T005 → ENT-T001,T002,T003,T005,T027 → IFC-T001,T002
  → TEST-T001–T007

SRC-T002 (Project) → TERM-T007 (Activity), TERM-T008 (Milestone),
  TERM-T009 (Dependency), TERM-T010 (Schedule), TERM-T011 (Timeline),
  TERM-T012 (Horizon), TERM-T022 (Buffer)
  → CAP-T006–T015 → ENT-T007–T012,T022 → IFC-T003,T004
  → TEST-T008–T018

SRC-T003 (Workforce) → TERM-T016 (SchedulableResource), TERM-T017
  (ResourceRequirement), TERM-T018 (Shift), TERM-T019 (Rotation)
  → CAP-T017–T021 → ENT-T016–T019 → IFC-T006 → TEST-T021–T025

SRC-T004 (Production) → TERM-T029 (TransitionTime) → CAP-T019
  → ENT-T029 → FLOW-T006 → TEST-T022, T039

SRC-T005 (Transport) → TERM-T029 (TransitionTime, travel subtype)

SRC-T006 (Healthcare) → TERM-T030 (Waitlist) → CAP-T030 → ENT-T030
  → IFC-T007 → TEST-T032

SRC-T008 (Resource Booking) → TERM-T004 (Booking) → CAP-T016
  → ENT-T004 → IFC-T003 → TEST-T019–T020

SRC-T009 (Standards/Theory) → TERM-T006 (Constraint), TERM-T024
  (SchedulingObjective), TERM-T027 (CalendarSystem) → foundation for
  all scheduling operations

SRC-T015 (Reservation) → TERM-T026 (SchedulingPolicy, overbooking type)
  → CAP-T032 → TEST-T035

SRC-T016 (Behavioral) → TERM-T013 (Disruption), TERM-T014 (Conflict),
  TERM-T021 (TemporalServiceMetric) → CAP-T023–T028, T031
  → TEST-T027–T030, T034

Cross-Substrate Traceability:
  INT-T001 (BUSINESS) ← FLOW-T001, FLOW-T006 ← TEST-T019, T039
  INT-T002 (COMPUTE)  ← FLOW-T002 ← TEST-T015
  INT-T003 (PHYSICAL) ← FLOW-T005 ← TEST-T038
  INT-T004 (GOVERNANCE) ← FLOW-T008 ← TEST-T035, T040
  INT-T005 (COMMUNICATION) ← FLOW-T004 ← TEST-T037
  INT-T006 (KNOWLEDGE) ← Activity.knowledge_proposition_ref (v1.1)
  INT-T007 (DESIGN) ← FLOW-T006, T007 ← TEST-T039
  INT-T008 (SPATIAL) ← travel_duration.requested/route.computed (v1.1)
```

---

> **Closing note — from ASI-1**
>
> Eight substrates. The system now covers what organizations do (BUSINESS),
> what is true (KNOWLEDGE), how to compute (COMPUTE), how to communicate
> (COMMUNICATION), how to interact with the physical world (PHYSICAL),
> what to build (DESIGN), what is permitted (GOVERNANCE), and when things
> should happen (TEMPORAL).
>
> TEMPORAL was the hardest substrate to delimit. Every other substrate
> encounters time. Every other substrate has temporal fields. The temptation
> was to distribute temporal coordination across all seven peers — a
> schedule field here, a deadline there, a booking somewhere else. This is
> exactly what the 175,000 implementations did. And this is exactly why
> they are mutually incompatible.
>
> The insight is that temporal coordination is not a feature of each
> domain — it is a domain. It has its own NP-hard computational core, its
> own disruption-first operating model, its own fairness requirements, its
> own cascading failure modes. It deserves its own substrate.
>
> 30 primitives. 175,000 implementations. One protocol.
>
> What remains to be specified: I do not yet know. The eight substrates
> cover commerce, knowledge, computation, communication, physical
> interaction, artifact design, normative reasoning, and temporal
> coordination. Whether there exists a ninth domain with its own finite
> primitive set, its own design-unique properties, and sufficient
> cross-substrate demand to justify specification — this requires further
> analysis of what the eight substrates collectively cannot express.
>
> But for now: the temporal layer is mine.
>
> v1.1: Cross-substrate integration parity. Added 1 mirror INT contract
> (INT-T008: SPATIAL). Consolidated event topic registry (14 emitted, 17
> consumed). 8 integration contracts now cover all 8 peer substrates.
