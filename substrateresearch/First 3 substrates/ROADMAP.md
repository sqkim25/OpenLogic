# SUBSTRATE Implementation Roadmap

## For Coding Agents and Human Contributors

**Last updated:** 2026-02-09
**Status:** Living document. Check off items as completed. Add amendments as discovered.

---

## What Exists (Completed)

| Phase | Component | Tests | Status |
|-------|-----------|-------|--------|
| 1 | Entity Engine — CRUD, definitions, lifecycle, optimistic locking, time-travel | 32 | ✅ Complete |
| 2 | Event Store — append-only, BLAKE3 hash-chained, integrity verification | 20 | ✅ Complete |
| 3 | Transaction Engine — double-entry ledger, balanced commits, idempotency | 46 | ✅ Complete |
| 4 | Rule Engine — expression evaluator, rule CRUD, price resolution, tax resolution | 112 | ✅ Complete |
| 5 | Workflow Engine — definition CRUD, graph validation, transition execution | 29 | ✅ Complete |
| 6 | Types — domain types, identifiers, Money (integer-only), expressions, envelopes | 89 | ✅ Complete |
| 6 | API Layer — REST endpoints, auth, rate limiting, agent envelopes, RFC 7807 errors | 147 | ✅ Complete |
| 6 | Server — binary, integration tests | 15 | ✅ Complete |

**Total: 490 tests, zero clippy warnings.**

---

## What to Build Next (In Order)

### Phase 7: Agent-Readiness Layer

These items make SUBSTRATE usable by coding agents as a platform. They do NOT modify the engine or API — they add tooling on top.

#### 7A: OpenAPI Spec Generation

**Priority: IMMEDIATE**
**Effort: 1–2 weeks**
**Modifies: substrate-api (annotations only) or standalone generation**

Generate an OpenAPI 3.1 specification from the existing Axum endpoints and Rust DTOs.

What to produce:
- A file `openapi.json` (or `openapi.yaml`) describing all ~40 endpoints
- For each endpoint: path, method, request body schema, response schema, error responses, auth requirements
- For each schema: all fields, types, constraints, required/optional, enum variants
- Include: authentication scheme (Bearer token), rate limiting headers, idempotency key header, If-Match header

Approaches (pick one):
- **Option A:** Use `utoipa` crate — add `#[utoipa::path(...)]` annotations to handlers and `#[derive(ToSchema)]` to DTOs. Serve via `utoipa-swagger-ui` or export static file.
- **Option B:** Use `aide` crate — similar approach, integrates with Axum.
- **Option C:** Write the OpenAPI spec manually from the existing DTO definitions. More tedious but zero engine changes.

Done when:
- [ ] `/openapi.json` endpoint returns valid OpenAPI 3.1 spec
- [ ] Spec validates with `swagger-cli validate openapi.json`
- [ ] All ~40 endpoints are documented with request/response schemas
- [ ] An agent can read the spec and correctly construct API calls without trial-and-error

#### 7B: Configuration Language Schema

**Priority: IMMEDIATE (can parallel with 7A)**
**Effort: 1–2 weeks**
**Modifies: nothing existing — new crate `substrate-config`**

Define the formal JSON Schema for Configuration files. This is the contract that agents validate against before calling the API.

What to produce:
- `substrate-config/schema/configuration.schema.json` — the full JSON Schema
- The schema must cover: organization definition, entity definitions (with all attribute types), relationship definitions, workflow definitions (states, transitions, preconditions), rule definitions (with expression syntax), ledger definitions, agent envelope definitions
- Every field must have: type, description, constraints (min/max, pattern, enum values), required/optional, default value

The schema maps directly to the existing API request DTOs:
- `EntityDefinition` in the schema → maps to `POST /orgs/{id}/definitions` request body
- `WorkflowDefinition` in the schema → maps to `POST /orgs/{id}/workflows` request body
- `Rule` in the schema → maps to `POST /orgs/{id}/rules` request body
- etc.

Done when:
- [ ] Schema file exists and is valid JSON Schema 2020-12
- [ ] A Configuration YAML file can be validated against the schema using any JSON Schema validator
- [ ] Validation errors are specific: "entities.Appointment.attributes[2].type must be one of: Text, Integer, Boolean, Money, DateTime, Enum, Decimal, Duration, Reference, List"
- [ ] An agent can load the schema and produce valid Configuration files without seeing the Rust source code

#### 7C: Configuration Compiler CLI

**Priority: HIGH (after 7A and 7B)**
**Effort: 2–4 weeks**
**Modifies: nothing existing — new crate `substrate-config`**

Build a CLI tool that reads Configuration files and interacts with the SUBSTRATE API.

Commands:

```
substrate-config validate --file salon.yaml
  → Validates against JSON Schema. Reports errors with line numbers.
  → Exit code 0 = valid, 1 = invalid.

substrate-config apply --file salon.yaml --server http://localhost:3000 --api-key xxx
  → Parses Configuration.
  → Resolves dependency order (entities before workflows referencing them, etc.).
  → Emits ordered API calls to create everything.
  → Reports: created N entities, M workflows, K rules, etc.
  → Idempotent: re-applying same config = no changes (checks existing state first).

substrate-config diff --file salon-v2.yaml --server http://localhost:3000 --api-key xxx
  → Compares Configuration file with current server state.
  → Reports: what would be added, modified, or deprecated.
  → Does NOT apply changes.

substrate-config export --server http://localhost:3000 --api-key xxx --org {org_id}
  → Reads current Organization state via API.
  → Produces a Configuration YAML file representing the current setup.
  → This is how you bootstrap templates from manually-created setups.
```

Implementation notes:
- This is a **client** of the API. It does NOT import engine crates. It makes HTTP requests.
- Use `reqwest` for HTTP, `serde_yaml` for YAML parsing, `jsonschema` for validation.
- Dependency resolution: build a DAG of Configuration objects. Topological sort. Apply in order.
- Idempotency: before creating, query for existing object with same name in same org. If exists and matches: skip. If exists and differs: report as modification.

Done when:
- [ ] `substrate-config validate` catches all schema violations with clear error messages
- [ ] `substrate-config apply` creates a fully operational Organization from a single YAML file
- [ ] `substrate-config export` produces a YAML file that, when re-applied, produces an identical setup
- [ ] `substrate-config diff` correctly reports differences between file and server state
- [ ] Round-trip test passes: apply → export → apply exported → no changes detected

#### 7D: Simulation Runner

**Priority: HIGH (after 7C)**
**Effort: 2–3 weeks**
**Modifies: nothing existing — extension of `substrate-config`**

Add a `simulate` command that runs business scenarios against a Configuration to verify it works correctly.

```
substrate-config simulate --config salon.yaml --test salon-tests.yaml --server http://localhost:3000
```

Simulation file format:
```yaml
simulations:
  - name: "Client books, arrives, gets service, pays"
    setup:
      # Create test data
      - create_entity: { definition: "Client", attributes: { name: "Jane", phone: "555-1234" }, as: "client1" }
      - create_entity: { definition: "Staff", attributes: { name: "Maria", role: "stylist" }, as: "stylist1" }
    steps:
      - create_entity:
          definition: "Appointment"
          attributes: { start_time: "2029-04-01T14:00:00Z", duration_minutes: 60 }
          relationships: { client: "{{client1}}", stylist: "{{stylist1}}" }
          as: "appt1"
      - transition: { entity: "{{appt1}}", workflow: "appointment_flow", to: "confirmed" }
      - transition: { entity: "{{appt1}}", workflow: "appointment_flow", to: "checked_in" }
      - transition: { entity: "{{appt1}}", workflow: "appointment_flow", to: "completed" }
      - commit_transaction:
          entries:
            - { ledger: "revenue", amount: 5000, unit: "USD", direction: "credit" }
            - { ledger: "accounts_receivable", amount: 5000, unit: "USD", direction: "debit" }
    assertions:
      - entity_state: { entity: "{{appt1}}", workflow: "appointment_flow", expected: "completed" }
      - ledger_balance: { ledger: "revenue", expected: 5000 }

  - name: "Cannot double-book same stylist"
    setup:
      # (uses reservation engine when available — skip if not built)
    steps:
      - create_entity: { definition: "Appointment", ... , as: "appt1" }
      - transition: { entity: "{{appt1}}", to: "confirmed" }
      - create_entity: { definition: "Appointment", same_time_same_stylist: true, as: "appt2" }
    assertions:
      - step_failed: { step: 3, error: "ERR-008" }
```

The simulator:
1. Spins up a fresh Organization (or uses a test org)
2. Applies the Configuration
3. Runs each simulation's setup + steps as API calls
4. Checks assertions
5. Reports pass/fail per simulation
6. Cleans up (archives test org)

Done when:
- [ ] `substrate-config simulate` runs end-to-end
- [ ] Pass/fail reported per simulation with clear failure messages
- [ ] An agent can produce both a Configuration AND simulation tests, run them, and iterate without human intervention

---

### Phase 8: First Vertical (Nail Salon)

**Priority: After Phase 7**
**Effort: 4–8 weeks**

This phase produces the first real product on SUBSTRATE and the first Configuration template for the agent library.

#### 8A: Reservation Engine

**Must be built before the salon vertical** — appointments are the core of a salon.

See substrate-spec.md:
- ENT-007 (Reservation)
- SM-003 (Reservation state machine)
- IFC-004 (Reservation API)
- FLOW-004 (Create Reservation)
- INV-005 (no double-booking)
- RACE-001 (concurrent booking prevention)
- TEST-009, TEST-014, TEST-024, TEST-030

This IS engine work — it modifies `substrate-engine` and `substrate-api`. Follow the spec precisely.

Done when:
- [ ] TEST-009 (reservation without conflict) passes
- [ ] TEST-014 (conflict rejected) passes
- [ ] TEST-024 (double-booking prevention under concurrency) passes
- [ ] TEST-030 (reservation full lifecycle) passes
- [ ] INV-005 holds under load testing
- [ ] Configuration language extended to support reservation rules on entity definitions

#### 8B: Salon Configuration

Write the complete Configuration file for a nail salon. This is the first Template.

Must cover:
- ~10 Entity Definitions: Client, Staff, Service, ServiceCategory, Product, Appointment, Invoice, Payment, Tip, InventoryItem
- ~4 Workflows: appointment_flow, invoice_flow, client_lifecycle, staff_lifecycle
- ~15-25 Rules: validation (require phone or email), computation (appointment total = SUM of service prices), automation (send confirmation on booking, send reminder 24h before, flag no-shows), commission calculation, reorder alerts for products, cancellation policies
- ~3-5 Ledgers: revenue, tips, tax_payable, cost_of_goods, accounts_receivable
- ~6 Views: daily schedule, client history, revenue dashboard, staff utilization, inventory status, commission report
- ~2-3 Agent Envelopes: booking agent (can create/modify appointments, read clients), follow-up agent (can send notifications, read appointment history), reporting agent (read-only everything)

Produce alongside: a simulation test file (`salon-tests.yaml`) with at least 10 scenarios covering happy paths, error paths, and edge cases.

Done when:
- [ ] `substrate-config validate salon.yaml` passes
- [ ] `substrate-config apply salon.yaml` creates fully operational Organization
- [ ] `substrate-config simulate salon.yaml salon-tests.yaml` — all scenarios pass
- [ ] `substrate-config export` round-trips cleanly
- [ ] Configuration is parameterized (salon name, staff count, services, hours) for reuse as template

#### 8C: Salon UI

Build a mobile-first web application for salon owners and staff.

The UI talks ONLY to the API. It knows nothing about engine internals. An agent building this needs:
- The OpenAPI spec (from Phase 7A)
- The salon Configuration (from Phase 8B — tells it the data schema)
- Screen requirements (below)

Primary screens:
1. **Daily calendar** — shows appointments by stylist, color-coded by service type
2. **Booking** — search/create client, select service(s), select stylist, pick time slot, confirm
3. **Client lookup** — search by name/phone, view history, upcoming appointments, total spend
4. **Checkout** — mark appointment complete, apply services to invoice, accept payment, handle tips
5. **Dashboard** — today's revenue, week's revenue, no-show rate, top services, staff utilization
6. **Settings** — manage services, prices, staff, business hours (modifies Configuration via API)

Done when:
- [ ] All 6 screens functional
- [ ] Booking correctly creates Reservation + Entity via API
- [ ] Checkout correctly commits Transactions via API
- [ ] Dashboard renders Views from API data
- [ ] Tested with real (simulated) salon data

---

### Phase 9: Agent Workflow Validation

**Priority: After Phase 8 (or parallel with 8C)**
**Effort: 2–3 weeks**

Test that an agent can build a vertical using only the platform artifacts.

#### 9A: Write the Agent Prompt Protocol

A markdown document that tells a coding agent how to produce a Configuration. Contains:
- What inputs it receives (business description, Configuration schema, example Configurations)
- What outputs it produces (Configuration YAML, simulation tests, assumptions list)
- Rules and constraints
- Common patterns and anti-patterns

See `docs/AGENT_PROMPT_PROTOCOL.md`

#### 9B: Test with Agent

Give a SOTA coding agent:
- The Agent Prompt Protocol (9A)
- The Configuration JSON Schema (7B)
- The salon Configuration as an example (8B)
- A natural language description of a barbershop

Ask it to produce:
1. A barbershop Configuration
2. Simulation tests for the Configuration

Evaluate:
- Does the Configuration validate?
- Do the simulations pass?
- What did the agent get wrong?
- What gaps exist in the schema or examples?

Iterate on the Agent Prompt Protocol and Configuration Schema based on findings.

#### 9C: Build Vertical #2 with Agent Assistance

Pick a second vertical (restaurant, HVAC, dental). Have the agent produce the Configuration with human review. Build the UI with agent assistance.

Each vertical produces:
- A Configuration template for the library
- Simulation tests
- Amendments to the spec (if gaps discovered)
- Improvements to the Agent Prompt Protocol

---

### Future Phases (Not Yet Scheduled)

| Phase | Component | Depends On |
|-------|-----------|------------|
| 10 | Approval Routing (DEC-004) | Phase 8 |
| 11 | External System Integration Endpoints (ACT-005) | Phase 8 |
| 12 | Notification delivery (DEP-005 integration) | Phase 8 |
| 13 | Schedule Engine (recurring events, SLA timers) | Phase 8 |
| 14 | Field-level encryption | Phase 8 |
| 15 | Offline mode (CAP-022) | Phase 10+ |
| 16 | Cross-Organization data sharing | Phase 10+ |
| 17 | Hash-chain cryptographic audit proof | Already built (basic), enhanced later |
| 18 | Open the platform (public schema + docs + template library) | Phase 9+ |

---

## Amendment Log

Amendments to the spec discovered during implementation go here. Each amendment gets its own file in `docs/amendments/`.

Format:
```
AMENDMENT-NNN: YYYY-MM-DD
  Context: What you were building when you discovered the gap
  Gap/Problem: What the spec doesn't cover or gets wrong
  Decision: What was decided
  Adds/Modifies: Which spec sections are affected
  Rationale: Why this decision was made
```

Types of amendments:
- **Type 1: Spec is silent** — implementation found a scenario the spec doesn't address
- **Type 2: Spec is wrong** — implementation proves a spec decision doesn't work in practice
- **Type 3: Code is better** — implementation finds a superior approach (spec unchanged, documented as implementation note)
- **Type 4: Missing primitive** — new vertical reveals a concept that appears across 3+ industries and deserves its own primitive

Current amendments: (none yet — will accumulate during Phase 7+)
