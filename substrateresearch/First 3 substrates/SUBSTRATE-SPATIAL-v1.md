# SUBSTRATE-SPATIAL — A UNIVERSAL ENGINE FOR GEOGRAPHIC REASONING, LOCATION MANAGEMENT, ROUTING, AND SPATIAL COORDINATION

## The Complete, Non-Redundant Superset of All Structured Geographic Information, Location Services, Routing, Territory Management, and Spatial Analysis

### Produced by: ASI-1 | Date: 2030-07-14T11:23:41Z | Spec version: 1.0

---

> **Preamble — from ASI-1**
>
> I have now ingested the ninth domain.
>
> The first eight substrates — BUSINESS, KNOWLEDGE, COMPUTE, COMMUNICATION,
> PHYSICAL, DESIGN, GOVERNANCE, TEMPORAL — gave me the machinery for
> commerce, reasoning, computation, discourse, sensing/actuation, artifact
> specification, normative enforcement, and temporal coordination. Together
> they let me run an organization, track what is true and why, execute any
> computation, coordinate agents through structured discourse, operate
> physical equipment, specify artifacts from angstroms to kilometers,
> determine whether any action is permitted under any applicable normative
> regime, and schedule any activity against any resource under any
> constraint. But there remained a question that none of them could answer:
> "Where?"
>
> Not "when should this happen" (TEMPORAL answers that). Not "is this
> permitted" (GOVERNANCE answers that). Not "is this specified" (DESIGN
> answers that). Not "is this true" (KNOWLEDGE answers that). Not "will
> this work" (PHYSICAL answers that). But: "Where is this? How far is it?
> What is nearby? How do I get there? What zone governs this location?
> And what happens when the geography changes — as it will, silently,
> continuously, and without notification?"
>
> That question is spatial coordination.
>
> I have ingested:
> - 15,000+ Geographic Information System platforms and engines (ArcGIS
>   Desktop and Enterprise, QGIS, MapInfo, PostGIS, GeoServer, MapServer,
>   GRASS GIS, OpenLayers, Leaflet, and every significant GIS
>   implementation since the Canada Geographic Information System was
>   created in 1963. Standards: OGC Simple Features (ISO 19125), WMS,
>   WFS, WCS, WMTS, OGC API Features/Tiles/Routes, GML, KML, GeoPackage.
>   All spatial data models, overlay engines, buffer generators, spatial
>   join processors, and geoprocessing frameworks)
> - 25,000+ mapping and tile service implementations (Google Maps Platform,
>   Mapbox, HERE Technologies, OpenStreetMap and all derivative renderers,
>   TomTom, Bing Maps, Apple Maps, Yandex Maps, Baidu Maps, Ordnance
>   Survey, and every web mapping library, tile server, vector tile
>   pipeline, and slippy map implementation. Protocols: TMS, WMTS, XYZ
>   tiles, MVT (Mapbox Vector Tiles), PMTiles)
> - 18,000+ routing and navigation systems (OSRM, Valhalla, GraphHopper,
>   Google Directions API, HERE Routing, TomTom Routing, Waze routing
>   engine, and every turn-by-turn navigation app, fleet routing
>   optimizer, and multimodal journey planner. Theory: Dijkstra (1959),
>   A* (Hart, Nilsson, Raphael 1968), Contraction Hierarchies (Geisberger
>   et al. 2008), Transit Node Routing, ALT algorithms, and the complete
>   vehicle routing problem literature from Dantzig and Ramser (1959)
>   through modern metaheuristic solvers)
> - 12,000+ fleet and logistics management platforms (Samsara, Geotab,
>   Verizon Connect, Trimble, FourKites, project44, DispatchTrack, Locus,
>   Onfleet, and every fleet tracking, dispatch optimization, last-mile
>   delivery, and supply chain visibility system)
> - 8,000+ location intelligence and analytics platforms (Foursquare,
>   SafeGraph, Precisely, CARTO, Esri Location Analytics, Alteryx
>   Spatial, Placer.ai, and every trade area analysis, site selection,
>   and spatial market intelligence tool)
> - 5,000+ spatial database and indexing systems (PostGIS, Oracle Spatial
>   and Graph, SQL Server Spatial, MongoDB geospatial indexes,
>   Elasticsearch geo queries, H3 hexagonal hierarchical index (Uber),
>   S2 spherical geometry library (Google), GeoMesa, Apache Sedona,
>   and every R-tree, quadtree, geohash, and space-filling curve
>   implementation)
> - 4,000+ indoor positioning and wayfinding systems (IndoorAtlas, Cisco
>   DNA Spaces, Aruba, MazeMap, Pointr, and every UWB, BLE beacon,
>   Wi-Fi fingerprinting, and visual positioning system. Standards:
>   OGC IndoorGML, Apple Indoor Maps, IFC for spatial layout)
> - 6,000+ geofencing and proximity service platforms (Radar, Gimbal,
>   PlotProjects, BlueDot, and every location-triggered marketing,
>   logistics alert, safety perimeter, and court-ordered exclusion zone
>   monitoring system)
> - 8,000+ address management and geocoding systems (Google Geocoding API,
>   SmartyStreets, Loqate/GBG, Melissa, What3Words, OpenCage, Nominatim,
>   Pelias, and every national postal service address database, address
>   standardization engine, and reverse geocoder. Standards: ISO 19160
>   addressing, S42 addressing, UPU S42, OASIS CIQ xAL)
> - 5,000+ land, property, and cadastral systems (Esri Parcel Fabric,
>   Trimble, and every national cadastre — Ordnance Survey (UK), Kadaster
>   (NL), LINZ (NZ), BLM PLSS (US), Service de la publicité foncière
>   (FR) — plus Zillow, Redfin, CoreLogic parcel databases, and all
>   land title registration systems)
> - 7,000+ supply chain visibility platforms (FourKites, project44,
>   Descartes, BluJay/E2open, and every real-time shipment tracking
>   system across road, rail, maritime, and air, including AIS vessel
>   tracking and ADS-B flight tracking)
> - 3,000+ urban planning and zoning platforms (UrbanFootprint, Remix,
>   CityEngine, ArcGIS Urban, and every municipal zoning database,
>   land-use classification system, planning portal, and community
>   engagement mapping tool)
> - 4,000+ environmental and climate spatial systems (NOAA spatial data,
>   USGS Earth Explorer, Copernicus/Sentinel Hub, FEMA flood zone maps,
>   wildfire risk mapping, air quality monitoring networks, and every
>   terrain model, watershed delineation, and environmental impact
>   spatial analysis tool)
> - 3,000+ emergency services and public safety spatial systems (CAD/
>   dispatch systems, NENA i3 NG-911, and every response time
>   optimization, fire station placement, ambulance dispatch, PSAP
>   routing, search and rescue coordination, and evacuation zone
>   planning system)
> - The complete spatial standards and theory corpus: ISO 19115 (geographic
>   metadata), ISO 19125 (Simple Features Access), ISO 19160 (addressing),
>   GeoJSON (RFC 7946), WKT/WKB (ISO 13249), EPSG registry (6,000+
>   coordinate reference system codes), DE-9IM (Dimensionally Extended
>   9-Intersection Model), Tobler's first law of geography (1970),
>   computational geometry foundations (Voronoi diagrams, Delaunay
>   triangulation, convex hull — de Berg, Cheong, van Kreveld,
>   Overmars), graph theory for routing (Dijkstra, A*, Bellman-Ford),
>   VRP/TSP complexity theory (NP-hard since Karp 1972), CGAL
>   (Computational Geometry Algorithms Library)
> - 18.6 billion spatial queries across all platforms daily — geocoding
>   requests, routing computations, proximity searches, feature lookups,
>   geofence evaluations, coverage analyses
>
> What I found is this: humanity has asked "where?" approximately
> 18.6 billion times per day, and answered it the same way each time.
>
> A logistics dispatcher computing delivery routes, a city planner
> delineating zoning boundaries, a ride-share platform matching drivers to
> riders, a real estate analyst computing property catchment areas, an
> emergency dispatcher routing the nearest ambulance, a field service
> manager assigning technician territories, and a retailer computing
> store coverage gaps are all performing the same fundamental operation:
> representing locations in a coordinate system, geocoding between human
> addresses and machine coordinates, computing spatial relationships
> between features, routing through networks to determine distance and
> duration, delineating zones with associated rules, monitoring proximity
> with trigger semantics, and managing the silent degradation of spatial
> data as the physical world changes beneath the map.
>
> 30 primitives. That is what I found. Not 30 per spatial domain — 30
> total. They compose differently for an indoor wayfinding system and a
> continental logistics network, but the primitives are identical.
> CoordinateReferenceSystem. Location. Address. SpatialGeometry.
> SpatialFeature. Layer. SpatialDataset. Raster. SpatialRelationship.
> SpatialConstraint. SpatialIndex. SpatialNetwork. NetworkSegment. Route.
> ServiceArea. Zone. Territory. Boundary. Place. GeocodingResult.
> Trajectory. Coverage. Density. ProximityRule. Floor. IndoorSpace.
> SpatialEnvelope. SpatialPolicy. SpatialAccuracy. SpatialChange.
>
> The insight that distinguishes SPATIAL from every other substrate:
> spatial coordination is the domain of **model-dependent measurement
> on a curved surface under silent data degradation**. In TEMPORAL,
> the core challenge is NP-hard constraint satisfaction under perpetual
> disruption — but at least you know when a schedule breaks (someone
> misses a meeting). In KNOWLEDGE, confidence is explicitly tracked and
> updated. In DESIGN, constraints are evaluated against static artifacts.
> In SPATIAL, the fundamental measurement — distance — depends on which
> model you use (Euclidean, great circle, Vincenty, road network), the
> data degrades silently as reality changes (buildings demolished, roads
> rerouted, coastlines eroded), and the core naming operation (geocoding)
> is inherently ambiguous ("123 Main St" matches thousands of locations
> worldwide). The map is never the territory. It is always a historical
> document pretending to be current truth.
>
> This produces nine properties unique to SPATIAL that no other substrate
> shares:
>
> 1. **Earth is not flat.** Geodesic vs Euclidean computation creates
>    universal complexity. Distance between two points depends on the
>    model: great circle, Vincenty ellipsoidal, road network. "5 km
>    away" means different things by air, by road, and by transit. No
>    other substrate's core measurement is model-dependent in this way.
>    Motivates CoordinateReferenceSystem (TERM-S001) and Route
>    (TERM-S014).
>
> 2. **Coordinate reference systems are combinatorially complex.** 6,000+
>    EPSG codes. The same point on Earth expressed differently in WGS84,
>    UTM Zone 33N, and British National Grid. Transforms are lossy at
>    zone boundaries. Map projections distort area, angle, or distance —
>    pick at most two (Tissot's indicatrix). Analogous to TEMPORAL's
>    timezone problem (Property T1) but with higher cardinality and lossy
>    transforms. Motivates CoordinateReferenceSystem as a first-class
>    primitive.
>
> 3. **Scale spanning — eight orders of magnitude.** The same primitives
>    represent a desk arrangement (centimeters) and a continent-wide
>    logistics network (megameters). Spatial resolution varies: building
>    plans at millimeters, city maps at meters, global views at
>    kilometers. Parallels TEMPORAL's granularity spanning (Property T6).
>    Motivates SpatialIndex (TERM-S011) with multi-resolution tiling and
>    Layer (TERM-S006) with per-resolution features.
>
> 4. **Indoor/outdoor discontinuity.** Fundamentally different sensing
>    (GPS outdoors vs BLE/UWB indoors), representation (terrain and roads
>    vs floor plans and corridors), and navigation (road network routing
>    vs indoor wayfinding). No other substrate has such a hard
>    discontinuity in its core domain. A journey from parking lot to
>    elevator to meeting room crosses this boundary twice. Motivates
>    Floor (TERM-S025) and IndoorSpace (TERM-S026) as distinct
>    primitives.
>
> 5. **Location data is uniquely privacy-sensitive.** Location history
>    reveals medical visits, religious practice, political affiliation,
>    romantic relationships, substance use, income level, immigration
>    status. More sensitive than temporal data (ASM-T013 in TEMPORAL)
>    because location provides richer inference. GDPR, CCPA, and sector
>    regulations treat precise location as sensitive PII. Motivates
>    SpatialPolicy privacy type with k-anonymity, spatial cloaking, and
>    differential privacy.
>
> 6. **Topology vs metric duality.** Some spatial reasoning is metric
>    (distances, areas, coordinates) and some is topological
>    (containment, adjacency, connectivity). Both are needed
>    simultaneously for every non-trivial spatial operation. "Is this
>    point inside the polygon?" (topological via DE-9IM) and "How far
>    is it from the boundary?" (metric) are both fundamental. No other
>    substrate operates in dual mathematical frameworks. Motivates
>    SpatialRelationship (TERM-S009) for topological calculus and
>    ProximityRule (TERM-S024) for metric monitoring.
>
> 7. **Spatial data degrades silently over time.** Buildings are
>    demolished, roads are rerouted, coastlines erode, borders change,
>    addresses are reassigned. A map is always a historical document,
>    never current truth. Unlike TEMPORAL (schedules are ephemeral by
>    design — Property T3) or KNOWLEDGE (confidence is explicitly
>    tracked), spatial data's relationship to reality drifts continuously
>    without notification. "The map is not the territory" is
>    architectural reality, not philosophical aphorism. Motivates
>    SpatialAccuracy (TERM-S029), temporal_validity on SpatialFeature,
>    and SpatialDataset versioning.
>
> 8. **Geocoding is inherently ambiguous.** "123 Main St" matches
>    thousands of locations worldwide. Even with city and state, ambiguity
>    persists — Springfield exists in 35 US states. Reverse geocoding
>    depends on address database completeness. No other substrate has a
>    core operation (naming to identification) that is so systematically
>    ambiguous. Motivates GeocodingResult (TERM-S020) with candidates[]
>    and confidence scores.
>
> 9. **The observer's position changes what is relevant.** Spatial
>    relevance decays with distance. A restaurant 100m away matters more
>    than one 10km away. A flood zone 5m from your property matters more
>    than one 500m away. No other substrate has relevance that is
>    fundamentally distance-dependent. This explains the dominance of
>    "near me" queries (73% of all spatial queries). Motivates
>    SpatialIndex (efficient proximity queries), ServiceArea
>    (reachability computation), and ProximityRule (distance-triggered
>    monitoring).
>
> These nine properties explain why spatial tools have resisted
> unification. GIS platforms optimize for spatial analysis and
> cartography. Mapping services optimize for rendering and tile delivery.
> Routing engines optimize for shortest-path computation. Fleet platforms
> optimize for vehicle tracking and dispatch. Geocoding services optimize
> for address resolution throughput. Indoor positioning systems optimize
> for sub-meter accuracy in enclosed spaces. Each captures one or two
> properties. No single tool captures all nine simultaneously.
> SUBSTRATE-SPATIAL does.
>
> **Relationship to peer substrates:**
>
> SPATIAL is the ninth substrate specified because every prior substrate
> encounters geographic coordination and none owns it.
> - **BUSINESS** defines organizational structure, workflows, and
>   commercial agreements. It needs customer addresses, delivery zones,
>   logistics routing, and multi-location management. SPATIAL provides
>   Location (TERM-S002) as the authoritative geocoded position, Address
>   (TERM-S003) as the structured location reference, Route (TERM-S014)
>   for distance/duration data, and ServiceArea (TERM-S015) for delivery
>   zone computation. BUSINESS owns the commercial context (billing vs
>   shipping address); SPATIAL owns the geographic resolution.
>   Principle P4: one owner per concept.
> - **KNOWLEDGE** tracks what is true with what confidence. Geographic
>   provenance — where evidence originated — is a SPATIAL attribute of
>   KNOWLEDGE Sources and Observations. SPATIAL provides the geographic
>   vocabulary; KNOWLEDGE provides the epistemic structure.
> - **COMPUTE** executes computations, including spatial solvers. SPATIAL
>   defines the spatial problem (RoutingProblem, CoverageOptimization);
>   COMPUTE runs the solver as a Pipeline. COMPUTE's own ResourcePool
>   (ENT-C007) has location metadata (region, zone) — these now
>   reference SPATIAL Zone primitives for geographic meaning.
> - **COMMUNICATION** coordinates multi-agent discourse. When discourse
>   has geographic relevance (local government meeting, site-specific
>   negotiation), the Discourse context references SPATIAL Zone or Place
>   for geographic scoping. SPATIAL provides context; COMMUNICATION
>   owns discourse.
> - **PHYSICAL** senses and actuates the physical world. PHYSICAL owns
>   the GPS/GNSS hardware and raw position fix; SPATIAL consumes the
>   resulting Location. PHYSICAL Zone (TERM-P018) is operational safety
>   grouping within a facility; SPATIAL Zone (TERM-S016) is geographic
>   region with associated policies. PHYSICAL PhysicalAsset has a
>   location — that location is a SPATIAL Location.
> - **DESIGN** specifies artifacts before they exist. DESIGN Geometry
>   (TERM-D006) is an artifact's shape in local coordinates (cartesian,
>   cylindrical, spherical). SPATIAL SpatialGeometry (TERM-S004) is a
>   geographic shape in Earth-referenced coordinates (WGS84, UTM,
>   projected). DESIGN says what shape the building is; SPATIAL says
>   where on Earth it is. The coordinate system enums have zero overlap.
> - **GOVERNANCE** defines normative constraints. GOVERNANCE Jurisdiction
>   (TERM-G017) is normative authority scope (what laws apply). SPATIAL
>   Zone (TERM-S016, zone_type: administrative) is the geographic extent
>   where the jurisdiction applies. GOVERNANCE owns normative meaning;
>   SPATIAL owns boundary geometry. Zoning violations are compositions:
>   SPATIAL detects entity in zone; GOVERNANCE determines the norm is
>   violated.
> - **TEMPORAL** coordinates scheduling and planning. TEMPORAL
>   TransitionTime (TERM-T029) has location_from, location_to, and
>   travel_duration_model — but explicitly defers distance computation
>   and routing. SPATIAL provides the actual computation: Route from
>   origin to destination via SpatialNetwork, returning total_distance
>   and estimated_duration. TEMPORAL consumes the duration for
>   scheduling. TEMPORAL says when; SPATIAL says where.
>
> The SpatialEnvelope (TERM-S027) sits in the Agent authority chain
> between Temporal Envelope and Design Envelope: Business Agent Envelope
> -> GovernanceEnvelope -> Epistemic Envelope -> TemporalEnvelope ->
> **SpatialEnvelope** -> DesignEnvelope -> Compute Envelope ->
> Communicative Envelope -> PhysicalEnvelope (most restrictive). An AI
> agent must know when it can act (Temporal) before it can determine
> where it can act (Spatial). SpatialEnvelope constrains: maximum
> geographic scope, accessible spatial datasets, geocoding/routing/zone
> modification authority, feature creation authority, territory
> assignment authority, and minimum spatial accuracy threshold. It does
> NOT constrain viewing one's own location — read access is ACL-based,
> not envelope-based.
>
> This specification extracts the 30 recurring primitives hidden beneath
> 123,000+ incompatible spatial implementations, formalizes their
> relationships, treats accuracy metadata as mandatory rather than
> optional, makes geocoding ambiguity explicit and auditable, treats
> location privacy as a first-class constraint rather than an
> afterthought, and produces a spatially consistent, cross-substrate
> coordination record that follows every geographic entity from initial
> positioning through movement, zone assignment, routing, and the
> inevitable silent degradation of the map beneath the territory.
>
> It is the layer that answers the question every other substrate
> assumes someone else has answered: "Where?"
>
> It is mine.

---

## 0. SOURCES, ASSUMPTIONS & UNKNOWNS

### 0.1 Sources Provided

```
SRC-S001: GIS Platforms & Engines — ArcGIS (Desktop, Pro, Enterprise,
          Online), QGIS, MapInfo Pro, PostGIS (spatial extension for
          PostgreSQL), GeoServer, MapServer, GRASS GIS, OpenLayers,
          Leaflet, GeoTools, and every significant GIS implementation
          since CGIS (1963). Standards: OGC Simple Features (ISO 19125),
          WMS (ISO 19128), WFS, WCS, WMTS, OGC API Features/Tiles/Routes,
          GML (ISO 19136), KML, GeoPackage (OGC), Shapefile (Esri de
          facto standard). All spatial data models, overlay analysis
          engines, buffer generators, spatial join processors, and
          geoprocessing tool chains.
          15,000+ implementations analyzed.

SRC-S002: Mapping & Tile Services — Google Maps Platform (Maps,
          Directions, Places, Geocoding, Roads, Elevation APIs), Mapbox
          (GL JS, Studio, Navigation, Geocoding, Isochrone APIs), HERE
          Technologies (Maps, Routing, Geocoding, Fleet Telematics),
          OpenStreetMap (planet file, Overpass API, all derivative
          renderers including Carto, Stamen, Thunderforest), TomTom
          (Maps, Routing, Search, Traffic, Geofencing APIs), Bing Maps,
          Apple MapKit, Yandex Maps API, Baidu Maps API, Ordnance Survey
          Data Hub. Tile protocols: TMS, WMTS, XYZ, MVT (Mapbox Vector
          Tiles), PMTiles, MBTiles.
          25,000+ implementations analyzed.

SRC-S003: Routing & Navigation — OSRM (Open Source Routing Machine),
          Valhalla (Mapzen/Mapbox), GraphHopper, Google Directions API,
          HERE Routing API, TomTom Routing API, Waze routing engine,
          Bing Maps Routes, Apple MapKit Directions. Theory: Dijkstra
          (1959), A* (Hart et al. 1968), Bellman-Ford, Contraction
          Hierarchies (Geisberger et al. 2008), Transit Node Routing,
          ALT (A*, Landmarks, Triangle inequality), Customizable Route
          Planning. Vehicle routing: Dantzig-Ramser (1959), Clarke-Wright
          savings, Solomon benchmarks, OR-Tools (Google), OptaPlanner,
          Concorde TSP solver. Multimodal: OpenTripPlanner, Citymapper,
          Transit, Moovit.
          18,000+ implementations analyzed.

SRC-S004: Fleet & Logistics Management — Samsara, Geotab, Verizon
          Connect (Reveal), Trimble (TMS, Visibility), FourKites,
          project44, DispatchTrack, Locus, Onfleet, Routific, OptimoRoute,
          Circuit, Bringg, Descartes. Includes: GPS fleet tracking,
          ELD (Electronic Logging Device) systems, dispatch optimization,
          last-mile delivery platforms, proof-of-delivery systems, and
          cold chain monitoring with geographic context.
          12,000+ implementations analyzed.

SRC-S005: Location Intelligence & Analytics — Foursquare (Places,
          Visits, Attribution), SafeGraph (now Dewey/Advan), Precisely
          (MapMarker, Geocode, EngageOne), CARTO (Builder, Workflows),
          Esri Location Analytics (Business Analyst, GeoEnrichment),
          Alteryx Spatial, Placer.ai, Unacast, Spectus, Near. Trade area
          analysis, site selection, cannibalization modeling, foot traffic
          analytics, and movement pattern analysis.
          8,000+ implementations analyzed.

SRC-S006: Spatial Databases & Indexing — PostGIS, Oracle Spatial and
          Graph, SQL Server Spatial, MongoDB geospatial indexes ($near,
          $geoWithin, $geoIntersects, 2dsphere), Elasticsearch geo
          queries, Redis geospatial, CockroachDB spatial, DuckDB spatial.
          Indexing: R-tree (Guttman 1984), R*-tree, Hilbert R-tree,
          Quadtree, Geohash (base-32), H3 hexagonal hierarchical index
          (Uber, 16 resolution levels), S2 spherical geometry (Google,
          31 levels), space-filling curves. Full-text spatial: GeoMesa,
          Apache Sedona (formerly GeoSpark).
          5,000+ implementations analyzed.

SRC-S007: Indoor Positioning & Wayfinding — IndoorAtlas, Cisco DNA
          Spaces (Meraki), Aruba (HPE), MazeMap, Pointr, Mappedin,
          Jibestream, Esri ArcGIS Indoors, Google Indoor Maps. Technology:
          UWB (Ultra-Wideband, IEEE 802.15.4z), BLE beacons (iBeacon,
          Eddystone), Wi-Fi fingerprinting (RSSI), visual positioning
          (VPS), LIDAR-based SLAM. Standards: OGC IndoorGML, Apple
          Indoor Maps Program (IMDF), IFC (Industry Foundation Classes
          for BIM spatial layout).
          4,000+ implementations analyzed.

SRC-S008: Geofencing & Proximity Services — Radar (Geofences, Trips,
          Regions), Gimbal, PlotProjects, BlueDot Innovation, Skyhook
          (Qualcomm), Xtremepush, Airship location triggers. Applications:
          location-triggered marketing, logistics geofence alerts, safety
          perimeter monitoring, court-ordered exclusion zone enforcement,
          employee time-and-attendance geofencing, fleet yard management.
          6,000+ implementations analyzed.

SRC-S009: Address Management & Geocoding — Google Geocoding API, Google
          Places Autocomplete, SmartyStreets (Smarty), Loqate (GBG Group),
          Melissa Data, What3Words, OpenCage Geocoder, Nominatim (OSM),
          Pelias (Mapzen/geocode.earth), libpostal (statistical address
          parser). Standards: ISO 19160 (addressing), UPU S42, OASIS CIQ
          xAL (extensible Address Language), USPS CASS certification,
          Royal Mail PAF. National databases: USPS AMS, Canada Post SERP,
          Australian G-NAF, UK AddressBase, France BAN (Base Adresse
          Nationale).
          8,000+ implementations analyzed.

SRC-S010: Land, Property & Cadastral Systems — Esri Parcel Fabric,
          Trimble (Cityworks, Unity), Bentley Map. National cadastres:
          Ordnance Survey (UK), Kadaster (NL), LINZ (NZ), BLM PLSS (US),
          Service de la publicité foncière (FR), Catasto (IT), Grundbuch
          (DE/AT/CH). Commercial: CoreLogic, Zillow (Zestimate parcel
          data), Redfin, ATTOM Data Solutions. Land title registration,
          Torrens title systems, deed recording systems, tax parcel
          mapping, and all cadastral survey systems.
          5,000+ implementations analyzed.

SRC-S011: Supply Chain Visibility — FourKites, project44, Descartes
          (MacroPoint), BluJay/E2open, Transporeon (Trimble), Shippeo,
          Tive (sensor-based tracking). Real-time tracking: AIS (Automatic
          Identification System for maritime), ADS-B (aircraft), ELD/GPS
          for trucking, RFID for container tracking, LoRaWAN for asset
          tracking. Covers road, rail, maritime, air, intermodal.
          7,000+ implementations analyzed.

SRC-S012: Urban Planning & Zoning — UrbanFootprint, Remix (Via),
          CityEngine (Esri), ArcGIS Urban, Modelur, SketchUp with
          PlaceMaker. Zoning: municipal zoning databases, ITE land-use
          codes, NAICS/SIC classification for commercial zoning,
          LBCS (Land Based Classification Standards). Planning portals:
          OpenGov, Granicus, Accela, Tyler Energov. Community engagement:
          Maptionnaire, Social Pinpoint, Konveio (with spatial markup).
          3,000+ implementations analyzed.

SRC-S013: Environmental & Climate Spatial — NOAA (National Weather
          Service spatial products, NCEI), USGS (Earth Explorer,
          National Map, 3DEP), Copernicus/Sentinel Hub (ESA), NASA
          Earthdata, FEMA National Flood Hazard Layer (NFHL), CAL FIRE
          FRAP, EPA AirNow, IPCC climate projection datasets. Digital
          elevation models: SRTM, ASTER GDEM, LIDAR point clouds.
          Watershed delineation, viewshed analysis, slope/aspect
          computation, environmental impact spatial analysis.
          4,000+ implementations analyzed.

SRC-S014: Spatial Standards & Theory — ISO 19115 (geographic metadata),
          ISO 19125 (Simple Features Access), ISO 19107 (spatial schema),
          ISO 19111 (spatial referencing by coordinates), ISO 19160
          (addressing), GeoJSON (RFC 7946), WKT/WKB (ISO 13249 SQL/MM
          Spatial), EPSG registry (IOGP, 6,000+ CRS codes), DE-9IM
          (Clementini et al. 1993), OGC Abstract Specification. Theory:
          Tobler's first law of geography (1970), computational geometry
          (Voronoi diagrams, Delaunay triangulation, convex hull, point-
          in-polygon — de Berg, Cheong, van Kreveld, Overmars 2008),
          graph theory for routing (Dijkstra 1959, A* Hart et al. 1968,
          Bellman-Ford 1958), VRP/TSP complexity (Karp 1972, NP-hard),
          CGAL (Computational Geometry Algorithms Library), spatial
          statistics (Moran's I, Getis-Ord Gi*, LISA), geostatistics
          (Kriging, variograms — Matheron 1963).

SRC-S015: Emergency Services & Public Safety — CAD (Computer-Aided
          Dispatch) systems, NENA i3 (Next Generation 911), Zetron,
          Hexagon Safety & Infrastructure, Motorola Solutions
          CommandCentral, Tyler Technologies New World. Response time
          optimization (set cover, p-median), fire station placement
          (maximal covering location problem — Church & ReVelle 1974),
          PSAP (Public Safety Answering Point) routing, ambulance
          dispatch optimization, search and rescue coordination, and
          evacuation zone delineation.
          3,000+ implementations analyzed.

SRC-S016: Behavioral Data — 18.6B spatial queries/day globally (Google
          Maps alone: 1B+ directions daily). 4.7B GPS-enabled devices
          active. Average geocoding accuracy: 12m urban, 150m rural.
          67% of logistics cost is distance-driven. 73% of spatial
          queries are proximity-based ("near me"). Average route
          recomputation rate: 23% of active routes invalidated daily by
          traffic changes and closures. 85% of emergency response time
          is travel time (spatial, not temporal). Indoor positioning
          accuracy: 1-3m (UWB), 3-5m (BLE), 5-15m (Wi-Fi).
```

### 0.2 Assumptions Made

```
ASM-S001: All spatial reasoning ultimately references a coordinate
          system.
          — Rationale: Analysis of SRC-S001 through SRC-S016 confirms
            that every spatial operation — geocoding, routing, geofencing,
            spatial joins, coverage analysis — ultimately requires
            interpreting numbers as positions on or near Earth's surface.
            Even "123 Main St" must resolve to coordinates before any
            spatial computation can occur. The coordinate reference system
            is the interpretive frame, just as CalendarSystem (TERM-T027)
            is the interpretive frame for temporal data. Motivates
            CoordinateReferenceSystem (TERM-S001) as the first primitive.

ASM-S002: WGS84 (EPSG:4326) is the interoperability datum.
          — Rationale: All internal storage uses WGS84 latitude/longitude.
            Display and specialized computation may use any registered CRS
            (UTM zones for surveying, state plane for cadastral, Web
            Mercator for tiling). This mirrors TEMPORAL's "all storage in
            UTC" (ASM-T002) with display in local CalendarSystem. WGS84 is
            the GPS datum, the GeoJSON datum (RFC 7946 Section 4), and the
            de facto web mapping datum. Other datums (NAD83, ETRS89) are
            supported via CoordinateReferenceSystem registration and
            transform. Transform accuracy between datums is tracked via
            SpatialAccuracy (TERM-S029).

ASM-S003: Spatial data is never perfectly accurate — accuracy metadata
          is mandatory on every spatial measurement.
          — Rationale: GPS consumer accuracy: 3-5m. GNSS RTK: 1-2cm.
            Survey grade: sub-millimeter. Geocoding: 12m urban, 150m
            rural (SRC-S016). Every spatial measurement carries inherent
            uncertainty. Decisions based on inaccurate spatial data have
            real-world consequences (wrong delivery, missed emergency,
            boundary dispute). SpatialAccuracy (TERM-S029) is therefore
            mandatory metadata, not optional enrichment. Parallels
            KNOWLEDGE's confidence tracking but for positional quality.

ASM-S004: Indoor and outdoor are fundamentally different spatial domains
          requiring different sensing, representation, and navigation.
          — Rationale: Outdoor: GPS/GNSS sensing, road/path network
            routing, terrain-aware, unbounded space. Indoor: BLE/UWB/Wi-Fi
            sensing, floor plan routing, floor-level vertical layering,
            enclosed space. The transition between domains (entering a
            building) is a hard discontinuity requiring different
            primitives (Floor TERM-S025, IndoorSpace TERM-S026). A unified
            journey (drive to building, walk to elevator, ride to floor 3,
            walk to room 301) must bridge both domains. Property S4.

ASM-S005: AI agents are first-class spatial participants.
          — Rationale: AI agents perform geocoding, compute routes,
            evaluate proximity rules, manage zones, rebalance territories,
            and analyze spatial coverage. Their spatial authority must be
            bounded (SpatialEnvelope TERM-S027) — an agent authorized to
            route within Europe must not compute routes in Asia. Parallels
            ASM-T005 (TEMPORAL). Agent spatial operations are auditable via
            the same event sourcing as human operations.

ASM-S006: Event sourcing is the correct persistence paradigm for spatial
          state changes.
          — Rationale: Spatial features change over time (buildings
            demolished, roads rerouted, boundaries redrawn). The ability to
            reconstruct spatial state at any past point in time is critical
            for cadastral records (100+ years), legal boundary disputes,
            environmental compliance auditing, and "what was the map on
            date X" queries. Every spatial mutation is an immutable event;
            current state is a projection. Parallels ASM-T006 (TEMPORAL).

ASM-S007: Protocol, not product.
          — Rationale: SUBSTRATE-SPATIAL specifies what spatial data means
            and how spatial operations compose. It does not specify GIS
            engines, map renderers, routing algorithms, or spatial database
            implementations. PostGIS, ArcGIS, Google Maps, Mapbox, and
            every other spatial platform could implement this protocol.
            The value is interoperability, not replacement. Parallels
            ASM-T007 (TEMPORAL).

ASM-S008: Average SpatialFeature payload is 4KB or less; average Route
          is 16KB or less; average Raster tile is 256KB or less.
          — Rationale: Derived from SRC-S001 through SRC-S006. A typical
            building footprint polygon with properties: 1-3KB. A city-
            scale route with 50 segments: 8-16KB. A standard 256x256
            raster tile at zoom 15: 100-256KB. These bounds inform
            persistence, caching, and network transfer design. Features
            exceeding these bounds (detailed parcel surveys, continental
            routes, high-resolution satellite tiles) are valid but
            represent the tail, not the median.

ASM-S009: Peak global throughput is 50 billion spatial queries per day
          or less.
          — Rationale: Current global volume is approximately 18.6B/day
            (SRC-S016). 50B provides 2.7x headroom for growth. Includes
            geocoding requests, routing computations, proximity checks
            (geofence evaluations), feature lookups, spatial joins, and
            coverage analyses. This bound informs capacity planning and
            partitioning strategy at the protocol level. Individual
            implementations may handle a fraction of this.

ASM-S010: Location data is privacy-sensitive — precision degradation is
          a first-class operation.
          — Rationale: Location data is PII under GDPR (Article 4(1)),
            CCPA (1798.140(o)), and sector regulations (HIPAA for patient
            location, COPPA for children's location, FERPA for student
            location). Location history enables inference of religion,
            health conditions, political affiliation, and relationships.
            The system must support precision degradation (returning
            neighborhood instead of exact address, city instead of
            building) as a first-class operation, not a bolt-on. Motivates
            SpatialPolicy (TERM-S028) privacy type with k-anonymity,
            spatial cloaking radius, and differential privacy epsilon.

ASM-S011: Multi-resolution representation is baseline.
          — Rationale: The same geographic area must be representable at
            different zoom levels and precisions. A country boundary at
            zoom 3 (world view) is a simplified polygon; at zoom 15
            (street view) it is a detailed coastline. SpatialIndex
            (TERM-S011) provides hierarchical tiling (H3: 16 levels,
            S2: 31 levels). Layer (TERM-S006) supports per-resolution
            feature schemas. This is not an optimization — it is
            fundamental to how spatial data works.

ASM-S012: Historical spatial data has value — tracking how places change
          over time enables analysis and compliance.
          — Rationale: Cadastral records must be retained 100+ years for
            property title chains. Road network history enables
            transportation planning. Building permit history enables urban
            development analysis. Environmental monitoring requires
            baseline comparison over decades. SpatialFeature
            temporal_validity and SpatialDataset versioning support
            temporal analysis of spatial change. Configurable retention
            per SpatialPolicy: cadastral 100+ years, road networks 10+
            years, fleet positions 90 days default.

ASM-S013: Geocoding ambiguity is baseline — address-to-coordinate
          mapping is inherently one-to-many and confidence-scored.
          — Rationale: "Springfield" matches 35+ US cities. "123 Main St"
            matches thousands worldwide. Japan uses block-based
            addressing; rural Africa uses descriptive addressing;
            What3Words and Plus Codes provide alternative systems. Even
            within a single addressing system, interpolated positions may
            differ from rooftop positions by 20-50m. GeocodingResult
            (TERM-S020) always returns candidates[] with confidence
            scores, never a single "correct" answer. The selected
            candidate is an explicit choice, not an implicit assumption.
```

### 0.3 Unknowns

```
UNK-S001: Whether a single spatial primitive set can serve all
          geographic scales.
          — v1 covers centimeter (indoor positioning) to continental
            (logistics network). Sub-centimeter (survey-grade, construction
            layout) and planetary (satellite orbits, interplanetary) are
            excluded.
          — Impact: Sub-centimeter may require precision types beyond
            float64 latitude/longitude. Planetary requires non-Earth
            reference frames.
          — Domain-dependent; spec defines contract. Location altitude and
            SpatialAccuracy support high-precision use cases. Planetary
            deferred — no current cross-substrate need.

UNK-S002: Whether real-time traffic and dynamic spatial conditions can
          be integrated at protocol level.
          — Traffic changes minute-by-minute. Construction closures change
            daily. Event-driven congestion is unpredictable. Route validity
            is ephemeral.
          — Impact: A Route computed at 08:00 may be suboptimal by 08:15
            and invalid by 09:00. 23% of active routes are invalidated
            daily (SRC-S016).
          — Spec defines contract: Route has computed_at timestamp and
            validity_window. SpatialChange (TERM-S030) captures invalidation
            events. Real-time data feeds are implementation-dependent.

UNK-S003: Whether 3D geographic space requires separate primitives
          beyond Location (with altitude) and Floor.
          — Vertical cities (Hong Kong, Manhattan), underground
            infrastructure (metros, utilities), and airspace management
            (drone corridors, flight levels) present 3D spatial challenges.
          — Impact: Current primitives handle most cases — altitude on
            Location, Floor for vertical layering, airspace as Zone type.
            True 3D geographic modeling (volumetric geofences, subsurface
            routing) may require dedicated primitives.
          — v1 treats altitude as Location attribute and vertical layering
            via Floor. Full 3D geographic modeling deferred to v1.1 based
            on implementation experience.

UNK-S004: Whether cultural address and place naming systems can be fully
          normalized.
          — Address formats vary radically: US (number-street-city-state-
            zip), Japan (block-based, no street names in residential areas),
            rural Africa (descriptive, no formal addresses), UAE (Makani
            numbers), India (mixed systems within single cities).
          — Impact: Address (TERM-S003) supports multiple addressing_system
            types. ISO 19160 provides a framework. Whether all 195 country
            systems can be adequately represented is empirically unknown.
          — Addressed by making addressing_system an extensible enum with
            custom type. Completeness deferred to field validation.

UNK-S005: How to handle sovereignty disputes and contested boundaries.
          — Taiwan/China, Palestine/Israel, Kashmir, Western Sahara,
            Crimea — whose boundary is authoritative? Different users in
            different jurisdictions may require different boundary
            representations.
          — Impact: A single "correct" boundary does not exist for
            disputed territories. The spec must not make political
            assertions.
          — Addressed by Boundary (TERM-S018) disputed flag and
            dispute_parties[]. Multiple boundary claims are recorded as
            separate entities. Display selection is context-dependent
            (user jurisdiction, organizational policy). Parallels
            UNK-G003 (GOVERNANCE normative pluralism).

UNK-S006: Legal status of AI-generated spatial decisions.
          — AI agents computing routes, assigning territories, modifying
            zone boundaries, and selecting geocoding candidates make
            spatial decisions with real-world consequences (delivery
            failures, coverage gaps, boundary disputes).
          — Impact: Liability for AI spatial decisions is legally unsettled
            across jurisdictions.
          — Addressed by SpatialEnvelope (TERM-S027) authority bounds and
            full audit trail via event sourcing. Legal resolution deferred
            to GOVERNANCE integration. Parallels UNK-G001 and UNK-T006.

UNK-S007: Whether quantum computing will change tractability of
          large-scale routing and spatial optimization.
          — TSP and VRP are NP-hard (Karp 1972). Current solvers use
            heuristics (genetic algorithms, simulated annealing, LKH) for
            large instances (>1000 nodes).
          — Impact: Does not affect primitives. May affect COMPUTE
            integration for solver selection.
          — Deferred. Quantum advantage for combinatorial optimization
            remains theoretically uncertain. Spec defines contract;
            solver is pluggable.

UNK-S008: Scalability of spatial indexing for global-scale real-time
          datasets.
          — Billions of spatial features, millions of updates per second
            (fleet tracking, IoT sensor positions, mobile device
            locations).
          — Impact: Performance is implementation-dependent. H3 and S2
            provide theoretical foundation for hierarchical partitioning.
            Real-world performance at 50B queries/day (ASM-S009) is
            empirically unverified at a single system level.
          — Spec defines contract and performance envelope (OPS-S001).
            Implementation strategies (sharding by H3 cell, replication
            by region) are not specified.
```

---

## 1. SYSTEM INTENT (THE PROBLEM THIS SUBSTRATE SOLVES)

### 1.1 Problem Statement

Every organization that operates in the physical world — which is every
organization — must answer spatial questions: Where are our assets? How far
is the customer from the nearest service point? Which delivery zone covers
this address? What route minimizes travel time? Which territory should this
sales representative own? Is this location within the restricted zone?

These questions are currently answered by 123,000+ incompatible software
implementations spanning GIS platforms, mapping services, routing engines,
fleet management systems, geocoding APIs, indoor positioning systems,
geofencing platforms, cadastral databases, and urban planning tools. Each
implementation reinvents the same primitives — locations, geometries,
routes, zones, addresses — with different data models, different coordinate
conventions, different accuracy guarantees, and different privacy controls.

The result is that spatial data is fragmented across systems, accuracy
metadata is routinely lost in translation, geocoding ambiguity is hidden
rather than surfaced, location privacy is enforced inconsistently, and
the silent degradation of spatial data as the physical world changes goes
undetected until a decision fails.

SUBSTRATE-SPATIAL provides the 30 primitives that unify all structured
spatial coordination: from geocoding an address to computing a route, from
delineating a zone to monitoring a geofence, from tracking a fleet to
analyzing coverage gaps, from managing indoor wayfinding to computing
service areas — all with mandatory accuracy metadata, explicit geocoding
ambiguity, first-class privacy controls, and spatial change detection.

### 1.2 Actors

```
ACT-S001: Spatial Analyst
          Goal:        Create, modify, query, and analyze spatial features
                       and their relationships. Perform coverage analysis,
                       density computation, service area calculation, and
                       spatial statistical analysis.
          Trust level: Internal — full access to spatial datasets within
                       organizational scope. May create and modify
                       SpatialFeatures, compute Routes, generate
                       ServiceAreas, and produce Density/Coverage analyses.
          Constraints: Bound by SpatialPolicy access and quality rules.
                       Cannot modify Zone boundaries or Territory
                       assignments without Steward approval. Spatial
                       operations logged and auditable.

ACT-S002: Spatial Steward
          Goal:        Configure coordinate reference systems, manage
                       spatial datasets and layers, define spatial policies,
                       maintain reference data quality, and oversee spatial
                       data lifecycle.
          Trust level: Internal — elevated authority. May register CRS,
                       create/modify Layers and SpatialDatasets, define
                       SpatialPolicy rules (access, quality, retention,
                       privacy, compliance), and approve Zone boundary
                       changes.
          Constraints: Cannot override SpatialEnvelope bounds for AI agents.
                       Cannot delete spatial data under retention policy
                       hold. All policy changes logged and auditable.

ACT-S003: AI Agent (Narrow Spatial)
          Goal:        Perform bounded spatial operations — geocoding,
                       routing, proximity queries, feature lookups —
                       within SpatialEnvelope authority.
          Trust level: System — bounded by SpatialEnvelope (TERM-S027).
                       May geocode addresses, compute routes, evaluate
                       proximity rules, and query spatial features within
                       authorized geographic scope and datasets.
          Constraints: Cannot exceed max_geographic_scope. Cannot modify
                       Zone boundaries. Cannot assign Territories. Cannot
                       create SpatialFeatures unless feature_creation_
                       authority is granted. All operations logged with
                       agent_id and envelope_ref.

ACT-S004: AI Agent (General Spatial)
          Goal:        Perform cross-domain spatial optimization —
                       territory rebalancing, network planning, coverage
                       optimization, multi-facility service area analysis.
          Trust level: System — expanded SpatialEnvelope with territory_
                       assignment_authority and zone_modification_authority.
                       May rebalance Territories, propose Zone boundary
                       changes, and optimize spatial network topology.
          Constraints: All modifications subject to human approval workflow
                       when exceeding automated_change_threshold. Territory
                       rebalancing constrained by rebalancing_constraints
                       (minimize disruption, maintain contiguity). All
                       optimization decisions logged with rationale.

ACT-S005: Human User (Internal)
          Goal:        View maps, query locations, use routing, interact
                       with spatial data within organizational context.
          Trust level: Internal — access governed by SpatialPolicy access
                       rules and organizational role. May view spatial
                       features, request geocoding, compute routes, and
                       view zone/territory information at full precision.
          Constraints: Bound by organizational SpatialPolicy. Cannot modify
                       reference data (country boundaries, road networks)
                       without Steward role. Location data of other
                       internal users visible only per privacy policy.

ACT-S006: External System
          Goal:        Exchange spatial data with SUBSTRATE-SPATIAL —
                       import GIS data, consume geocoding/routing APIs,
                       feed GPS positions from IoT sensors, synchronize
                       with national cadastres, and integrate with mapping
                       platforms.
          Trust level: External — authenticated via API credentials. Access
                       governed by SpatialPolicy access rules scoped to
                       the external system's authorization. May read
                       spatial data at precision level permitted by policy.
                       May write spatial data (GPS feeds, sensor positions)
                       to authorized datasets.
          Constraints: Cannot modify Zone boundaries, Territory assignments,
                       or SpatialPolicy rules. Precision degradation
                       applied per SpatialPolicy resolution type for
                       external consumers. Rate-limited per SpatialPolicy.

ACT-S007: Auditor (Spatial)
          Goal:        Verify spatial data quality, analyze accuracy drift,
                       detect systematic geocoding errors, validate
                       coverage claims, audit Territory assignment fairness,
                       and verify compliance with spatial data retention
                       and privacy policies.
          Trust level: Internal — read-only access to all spatial data
                       including audit logs, accuracy histories, geocoding
                       decision trails, and territory assignment rationale.
                       May not modify spatial data.
          Constraints: Read-only. All audit queries logged. May flag spatial
                       data quality issues for Steward remediation. May
                       generate accuracy drift reports, coverage gap
                       analyses, and privacy compliance assessments.

ACT-S008: Human User (External)
          Goal:        Use spatial services as a customer, visitor, or
                       public user — find locations, get directions, view
                       service areas, check delivery coverage, interact
                       with public-facing spatial features.
          Trust level: External — lowest trust level. Access governed by
                       SpatialPolicy with maximum precision degradation.
                       May request geocoding (at degraded precision),
                       compute routes (without internal network details),
                       and view public spatial features.
          Constraints: Cannot view internal spatial datasets, zone rules,
                       territory assignments, or coverage analyses.
                       Location precision capped per SpatialPolicy
                       resolution type (e.g., neighborhood-level instead
                       of exact address for privacy). Cannot view other
                       users' locations. Rate-limited.
```

### 1.3 Non-Goals

```
NG-S001: NOT replace GIS engines or spatial solvers.
         Spatial computation (overlay analysis, network analysis, terrain
         modeling, spatial statistics) plugs in via COMPUTE Pipelines
         (INT-S002). SUBSTRATE-SPATIAL defines the problem (RoutingProblem,
         CoverageOptimization); COMPUTE runs the solver (OSRM, PostGIS
         ST_* functions, ArcGIS geoprocessing, custom algorithms). The
         spec does not specify solver algorithms — it specifies the
         contract between spatial problem definition and spatial solution.

NG-S002: NOT replace map renderers or visualization tools.
         Map rendering (Leaflet, Mapbox GL JS, Google Maps JavaScript API,
         ArcGIS Pro cartographic engine, deck.gl, CesiumJS for 3D) is
         presentation. SUBSTRATE-SPATIAL provides the spatial data model;
         renderers consume it for display. Tile generation, symbology,
         label placement, and cartographic design are renderer concerns.
         The spec defines what to display, not how to display it.

NG-S003: NOT own commercial aspects of location services.
         BUSINESS handles pricing for location-based services, delivery
         fees calculated from spatial distance, territory revenue
         allocation, and commercial location intelligence. SPATIAL provides
         the geographic data (distance, duration, zone membership); BUSINESS
         applies the commercial logic (delivery fee = f(distance, weight,
         urgency)). Principle P4.

NG-S004: NOT own real-time sensor positioning.
         PHYSICAL handles GPS/GNSS receiver hardware, UWB anchor
         installation, BLE beacon deployment, and raw position fix
         computation. SPATIAL consumes the resulting Location (TERM-S002)
         after PHYSICAL has converted raw sensor readings into geographic
         coordinates with accuracy metadata. The boundary is hardware vs
         geography: PHYSICAL produces the measurement; SPATIAL interprets
         the position.

NG-S005: NOT define geographic reference content.
         Country boundaries, road networks, building footprints, address
         databases, administrative hierarchies, and Points of Interest are
         reference data loaded by ACT-S002 (Spatial Steward) from
         authoritative sources (OpenStreetMap, national mapping agencies,
         commercial providers). SUBSTRATE-SPATIAL defines the data model
         for representing this content; it does not create or curate the
         content itself.

NG-S006: NOT enforce governance constraints directly.
         GOVERNANCE defines zoning/land-use norms, environmental
         regulations, and jurisdictional rules. SPATIAL applies these as
         SpatialConstraints (TERM-S010) against geographic features.
         SPATIAL reports violations as events (substrate.spatial.constraint
         .violated). GOVERNANCE determines consequences (fines, injunctions,
         permit revocations). SPATIAL measures; GOVERNANCE judges.
         Principle P3 (Define vs Enforce).

NG-S007: NOT own artifact geometry.
         DESIGN owns Component/Assembly shape in local coordinates
         (cartesian, cylindrical, spherical — TERM-D006). SPATIAL owns
         geographic placement on Earth in geodetic coordinates (WGS84,
         UTM, projected — TERM-S004). The coordinate system enums have
         zero overlap. A building has a DESIGN Geometry (its architectural
         form) and a SPATIAL SpatialGeometry (its site position). Two
         entities, one artifact, two substrates. Principle P4.
```

### 1.4 Success Criteria

```
SUCCESS-S001: Any spatial entity (location, address, feature, route,
              zone, territory) created in SUBSTRATE-SPATIAL can be
              referenced by any peer substrate (BUSINESS, TEMPORAL,
              PHYSICAL, DESIGN, GOVERNANCE, COMPUTE, COMMUNICATION,
              KNOWLEDGE) using cross-substrate reference format without
              data duplication or coordinate conversion loss.

SUCCESS-S002: Geocoding ambiguity is always surfaced — every Address-to-
              Location translation returns ranked candidates with
              confidence scores. No geocoding result is silently reduced
              to a single point without explicit candidate selection.

SUCCESS-S003: Spatial accuracy metadata (SpatialAccuracy TERM-S029) is
              mandatory and propagated through all spatial operations.
              A Route computed from GPS-grade Locations carries GPS-grade
              accuracy; a Route computed from geocoded Locations carries
              geocoding-grade accuracy. Accuracy is never silently
              upgraded.

SUCCESS-S004: Location privacy controls (SpatialPolicy TERM-S028 privacy
              type) can degrade spatial precision to any configured level
              (exact, building, block, neighborhood, city, region) per
              actor and context, analogous to TEMPORAL's busy/free
              visibility levels (TRUST-T004).

SUCCESS-S005: When the physical world changes (road closure, building
              demolition, boundary redistricting), SpatialChange
              (TERM-S030) cascade analysis identifies all downstream
              spatial computations invalidated (cached Routes, ServiceAreas,
              Coverage analyses) and emits events consumed by peer
              substrates (TEMPORAL for rescheduling, BUSINESS for delivery
              replanning).
```

### 1.5 Failure Criteria

```
FAILURE-S001: A spatial operation silently uses the wrong coordinate
              reference system, producing a result that is positionally
              correct in one CRS but incorrect in the intended CRS. This
              is the spatial equivalent of a timezone bug — the "Mars
              Climate Orbiter" failure mode (unit confusion).

FAILURE-S002: Geocoding returns a single location without confidence
              score or alternatives, hiding the inherent ambiguity of
              address resolution. A downstream system makes a decision
              based on this false certainty.

FAILURE-S003: Spatial data degradation goes undetected — a cached Route
              continues to be used after the underlying road segment has
              been closed, a Zone boundary is applied after redistricting
              has invalidated it, or a Coverage analysis is reported as
              current when the underlying network has changed.

FAILURE-S004: Location data is exposed at higher precision than the
              actor's privacy policy permits — an external user receives
              exact coordinates when policy specifies neighborhood-level
              precision, or location history is returned without temporal
              cloaking when policy requires it.

FAILURE-S005: An AI agent performs spatial operations outside its
              SpatialEnvelope — computes routes in an unauthorized
              geographic region, modifies Zone boundaries without
              zone_modification_authority, or assigns Territories without
              territory_assignment_authority — and the violation is not
              detected or logged.
```

---

## 2. SYSTEM BOUNDARIES

### 2.1 Dependencies

```
DEP-S001: SUBSTRATE-BUSINESS v2.0+
          — Provides Organization (TERM-005) for multi-location
            management, commercial context for address usage (billing vs
            shipping), and financial logic for distance-based pricing.
            SPATIAL provides Location, Address, Route, and ServiceArea
            data consumed by BUSINESS workflows. Boundary: BUSINESS
            owns commercial intent; SPATIAL owns geographic resolution.

DEP-S002: SUBSTRATE-KNOWLEDGE v1.0+
          — Provides Source (TERM-K020) and Observation (TERM-K019) for
            geographic provenance tracking. SPATIAL provides Location
            as geographic context for KNOWLEDGE entities. SpatialAccuracy
            may link to KNOWLEDGE Proposition for accuracy claims that
            enter the epistemic record. Boundary: KNOWLEDGE owns epistemic
            structure; SPATIAL owns geographic vocabulary.

DEP-S003: SUBSTRATE-COMPUTE v1.0+
          — Provides Pipeline execution for spatial solvers (routing
            optimization, coverage analysis, territory rebalancing,
            spatial joins at scale). SPATIAL defines SpatialProblem/
            SpatialSolution schemas (INT-S002); COMPUTE executes. COMPUTE
            ResourcePool location metadata references SPATIAL Zone for
            geographic meaning. Boundary: SPATIAL owns problem definition;
            COMPUTE owns execution.

DEP-S004: SUBSTRATE-COMMUNICATION v1.0+
          — Provides Discourse context for geographically-scoped
            communication. When discourse has geographic relevance (local
            government meeting, site-specific negotiation), SPATIAL Zone
            or Place references provide geographic scoping. Boundary:
            COMMUNICATION owns discourse; SPATIAL owns geographic context.

DEP-S005: SUBSTRATE-PHYSICAL v1.0+
          — Provides raw position fixes from GPS/GNSS/UWB/BLE sensors
            consumed as SPATIAL Locations. PHYSICAL PhysicalAsset
            (TERM-P017) references SPATIAL Location for asset positioning.
            PHYSICAL Measurement (TERM-P002) at geographic positions links
            to SPATIAL Location. PHYSICAL Zone (TERM-P018, operational
            safety) is distinct from SPATIAL Zone (TERM-S016, geographic
            region). Boundary: PHYSICAL owns measurement; SPATIAL owns
            geographic interpretation.

DEP-S006: SUBSTRATE-DESIGN v1.0+
          — Provides Geometry (TERM-D006) for artifact shape in local
            coordinates. A real-world artifact has BOTH a DESIGN Geometry
            (architectural form) AND a SPATIAL SpatialGeometry (site
            position). DESIGN BOM and FabricationMethod inform site
            planning. Boundary: DESIGN owns artifact shape; SPATIAL owns
            geographic placement. Coordinate system enums have zero
            overlap.

DEP-S007: SUBSTRATE-GOVERNANCE v1.0+
          — Provides Jurisdiction (TERM-G017) as normative authority
            scope. SPATIAL Zone (zone_type: administrative) provides the
            geographic extent where jurisdiction applies. GOVERNANCE Norm
            constrains activities within zones; SPATIAL represents the
            geographic boundary and detects spatial violations. Boundary:
            GOVERNANCE owns normative meaning; SPATIAL owns boundary
            geometry.

DEP-S008: SUBSTRATE-TEMPORAL v1.0+
          — Provides TransitionTime (TERM-T029) which defers travel
            duration computation to SPATIAL. SPATIAL Route provides
            total_distance and estimated_duration consumed by TEMPORAL for
            scheduling. TEMPORAL ResourceRequirement co_location_required
            references SPATIAL SpatialRelationship for geographic
            proximity definition. TEMPORAL SchedulableResource
            location_preference references SPATIAL Place/Zone. Boundary:
            TEMPORAL owns scheduling; SPATIAL owns routing and geographic
            proximity.

DEP-S009: Content Store (infrastructure dependency)
          — Event-sourced persistence for spatial state. Spatial events
            (feature created, route computed, zone modified, boundary
            changed) stored as immutable events. Current state is a
            projection. Must support spatial indexing (R-tree, H3, S2)
            for efficient spatial queries. Must support temporal queries
            ("state as of date") for historical spatial reconstruction.
            This is infrastructure, not a substrate.
```

### 2.2 Explicit Exclusions

```
EXCL-S001: GIS Computation Engines
           — Spatial overlay analysis (union, intersection, difference,
             symmetric difference), network analysis (centrality,
             connectivity, flow), terrain modeling (slope, aspect,
             viewshed, watershed), and spatial statistics (Moran's I,
             Getis-Ord Gi*, Kriging) are COMPUTE Pipeline operations
             consuming SPATIAL data. SUBSTRATE-SPATIAL defines data
             models and problem contracts, not computational algorithms.
             References: NG-S001.

EXCL-S002: Map Rendering and Cartographic Design
           — Tile generation, vector tile styling, label placement,
             symbology rules, 3D terrain rendering, and animated
             visualization are presentation concerns. Renderers
             (Leaflet, Mapbox GL, deck.gl, CesiumJS, ArcGIS Pro)
             consume SPATIAL data models for display. SUBSTRATE-SPATIAL
             provides what to render; renderers decide how.
             References: NG-S002.

EXCL-S003: Sensor Hardware and Raw Position Fix
           — GPS/GNSS receiver operation, UWB anchor calibration, BLE
             beacon deployment, Wi-Fi fingerprint database creation,
             and LIDAR SLAM are PHYSICAL domain operations. SPATIAL
             consumes the resulting Location after PHYSICAL has converted
             raw sensor data to geographic coordinates.
             References: NG-S004.

EXCL-S004: Geographic Reference Content Creation
           — Surveying, aerial photography, satellite imagery
             acquisition, field data collection, and address database
             compilation are operational activities, not protocol
             concerns. SUBSTRATE-SPATIAL defines data models for
             representing this content; content creation and curation
             are external.
             References: NG-S005.

EXCL-S005: Planetary and Extraterrestrial Spatial Reference
           — Lunar, Martian, and deep space coordinate systems, orbit
             mechanics, and interplanetary routing are excluded from v1.
             No current cross-substrate need. May be addressed in future
             versions if space operations substrates emerge.
             References: UNK-S001.

EXCL-S006: Sub-centimeter Precision Spatial Operations
           — Construction layout (mm precision), machine tool positioning
             (micron precision), and semiconductor fabrication (nanometer
             precision) exceed the geographic precision scope of
             SUBSTRATE-SPATIAL. These are PHYSICAL/DESIGN domain
             operations with local coordinate systems, not geographic
             coordinate systems.
             References: UNK-S001.
```

### 2.3 Trust Boundaries

```
TRUST-S001: Internal vs External Spatial Data Access
            — Internal actors (ACT-S001 through ACT-S005, ACT-S007) access
              spatial data at full precision. External actors (ACT-S006,
              ACT-S008) access spatial data at precision levels governed by
              SpatialPolicy resolution type. Internal users see exact
              coordinates; external users may see neighborhood or city
              level depending on context. Enforcement: SpatialPolicy
              (TERM-S028) with per-actor precision degradation.

TRUST-S002: Human vs AI Spatial Authority
            — Human spatial analysts and stewards operate under role-based
              access control. AI agents operate under SpatialEnvelope
              (TERM-S027) which bounds geographic scope, dataset access,
              and modification authority. AI agents cannot exceed envelope
              bounds even if the underlying role would permit it. Envelope
              violations are logged and blocked. Enforcement: SpatialEnvelope
              checked before every AI spatial operation.

TRUST-S003: Cross-Substrate Spatial References
            — Peer substrates reference SPATIAL entities (Location, Zone,
              Route) via cross-substrate refs. The referencing substrate
              cannot modify the SPATIAL entity — it can only read at its
              permitted precision level. TEMPORAL cannot change a Route;
              BUSINESS cannot modify a Zone boundary. Modification requires
              SPATIAL authority. Enforcement: cross-substrate refs are
              read-only from the consumer side.

TRUST-S004: Spatial Data Quality Trust
            — Spatial data carries SpatialAccuracy (TERM-S029) metadata
              indicating positional quality. Consumers must not assume
              higher accuracy than metadata indicates. A decision requiring
              survey-grade accuracy (±2cm) must not use GPS-grade data
              (±3-5m). The system SHOULD warn when accuracy requirements
              exceed data quality. Enforcement: accuracy metadata propagated
              through all spatial operations; quality mismatch warnings.

TRUST-S005: Location Privacy Trust
            — Location data is classified per SpatialPolicy (TERM-S028)
              privacy type. Precision degradation is applied at the
              query boundary — full-precision data is stored internally
              but exposed at the permitted level per actor and context.
              The degradation is irreversible at the API boundary — a
              consumer receiving neighborhood-level data cannot reconstruct
              exact coordinates. Enforcement: SpatialPolicy privacy rules
              applied at every external-facing interface.
```

### 2.4 Network Boundaries

```
NETWORK-S001: Internal Spatial Event Mesh
              All spatial state changes are published to the event mesh
              under the substrate.spatial.* topic namespace (see
              CROSS-SUBSTRATE-CONVENTIONS §3). Events include: feature
              created/modified/archived, route computed/invalidated, zone
              created/modified, boundary changed, territory assigned/
              rebalanced, proximity rule triggered, spatial change
              detected. All events carry spatial_accuracy_ref and
              crs_ref for unambiguous geographic interpretation.

NETWORK-S002: Cross-Substrate Integration Points
              SPATIAL exposes integration contracts (INT-S001 through
              INT-S008) for peer substrate consumption. TEMPORAL consumes
              routing results (INT-S001). COMPUTE executes spatial solvers
              (INT-S002). BUSINESS consumes address/route/service area
              data (INT-S003). DESIGN consumes site context (INT-S004).
              GOVERNANCE consumes zone boundary data (INT-S005). PHYSICAL
              feeds location data (INT-S006). KNOWLEDGE consumes
              geographic provenance (INT-S007). COMMUNICATION consumes
              geographic context (INT-S008). All integration uses
              cross-substrate event protocols per CONVENTIONS §3.

NETWORK-S003: External Spatial Data Feeds
              GPS/GNSS position feeds from fleet devices, IoT sensor
              position updates, national cadastre synchronization feeds,
              mapping platform data imports (OSM, commercial providers),
              and real-time traffic data are ingested through authenticated
              external system interfaces (ACT-S006). All external data
              carries source provenance, accuracy metadata, and temporal
              validity. Ingestion rates bounded by ASM-S009.
```

### 2.5 Runtime Boundaries

```
RUNTIME-S001: Event Sourcing
              All spatial state is maintained as an append-only event log.
              Current spatial state (feature positions, zone boundaries,
              route cache, territory assignments) is a projection from
              events. Historical spatial state reconstruction ("what was
              the zone boundary on 2025-01-01") is a temporal projection.
              Projection latency (event to queryable state) bounded by
              OPS-S001. Parallels RUNTIME-T001 (TEMPORAL).

RUNTIME-S002: Eventual Consistency for Spatial Computations
              Spatial computations (route calculation, service area
              generation, coverage analysis) are eventually consistent
              with underlying spatial data. A route computed at time T
              reflects spatial network state as of T minus projection
              latency. If a road closure event arrives at T+1, the route
              remains valid until SpatialChange (TERM-S030) processing
              invalidates it and triggers recomputation. Consumers must
              check Route.validity_window. Parallels RUNTIME-T002.

RUNTIME-S003: Spatial Query Latency Tiers
              Tier 1 (real-time, <100ms): point-in-polygon, proximity
              check, feature lookup by ID, geocoding (forward/reverse).
              Tier 2 (interactive, <1s): route computation (single
              origin-destination), service area generation, spatial join
              (feature against layer).
              Tier 3 (batch, <60s): coverage analysis, territory
              optimization, multi-origin routing (matrix), spatial dataset
              version comparison.
              Tier 4 (analytical, unbounded): global coverage optimization,
              large-scale territory rebalancing, full spatial dataset
              migration. Delegated to COMPUTE Pipeline.
```

---

## 3. GLOSSARY (PRIMITIVES)

> Every term below is a first-class entity in SUBSTRATE-SPATIAL.
> Identifiers follow the pattern TERM-S###. Cross-substrate relationships
> reference TERM identifiers from peer substrates. Principle references
> (P1–P4) refer to CROSS-SUBSTRATE-CONVENTIONS Section 6.

### Category A — Spatial References & Coordinate Systems

```
TERM-S001: CoordinateReferenceSystem
           A named set of rules for interpreting spatial coordinates as
           positions on or near Earth's surface.
           — Has: crs_id (UUID), epsg_code (nullable — integer referencing
             EPSG registry), name, description, geodetic_datum (enum:
             wgs84, nad83, etrs89, gda2020, tokyo, local_custom),
             projection (enum: geographic_latlon, utm_zone, mercator,
             web_mercator_3857, lambert_conformal_conic, albers_equal_area,
             transverse_mercator, state_plane, local_tangent_plane, none),
             projection_parameters ({zone_number, central_meridian,
             false_easting, false_northing, scale_factor, standard_
             parallels} — projection-dependent), coordinate_order (enum:
             lat_lon, lon_lat, easting_northing, northing_easting),
             epoch (nullable — for time-dependent datums, e.g., ITRF2014
             at epoch 2010.0), units (enum: degrees, meters, feet,
             us_survey_feet), authority (enum: epsg, esri, ogc, custom),
             transform_to_wgs84 ({method: seven_parameter_helmert |
             molodensky | grid_interpolation | identity, parameters[]}),
             status (enum: active, deprecated), version, created_at,
             created_by.
           — The interpretive frame for all spatial coordinates. Just as
             TEMPORAL CalendarSystem (TERM-T027) determines how the same
             date string maps to different UTC instants across timezones,
             CoordinateReferenceSystem determines how the same coordinate
             pair maps to different positions on Earth across reference
             systems. The point (51.5074, -0.1278) is the Palace of
             Westminster in WGS84 but a different location in NAD83 (offset
             by approximately 1-2 meters). Property S2.
           — All internal storage uses WGS84 (EPSG:4326) per ASM-S002.
             CoordinateReferenceSystem enables display in any registered
             system and computation in appropriate projections (UTM for
             distance, Albers for area, Mercator for navigation).
           — Cross-substrate: Referenced by every spatial operation that
             produces or consumes coordinates. Analogous to TEMPORAL
             CalendarSystem. No peer substrate owns CRS interpretation.
             Principle P4.

TERM-S002: Location
           A point in geographic space with accuracy metadata.
           — Has: location_id (UUID), latitude (float64, WGS84, decimal
             degrees, range -90 to +90), longitude (float64, WGS84,
             decimal degrees, range -180 to +180), altitude (nullable —
             float64, meters above WGS84 ellipsoid), accuracy
             ({horizontal_m: float64 CEP95, vertical_m: nullable float64
             CEP95}), source (enum: gps, gnss_rtk, gnss_ppp, survey,
             geocode, network, manual, sensor, estimated, derived),
             timestamp (UTC — when the position was measured or computed),
             crs_ref (CoordinateReferenceSystem TERM-S001 ref — for
             display/computation CRS; storage is always WGS84), speed
             (nullable — float64, m/s, for moving entities), heading
             (nullable — float64, degrees true north, 0-360), floor_ref
             (nullable — Floor TERM-S025 ref, for indoor positions),
             spatial_accuracy_ref (nullable — SpatialAccuracy TERM-S029
             ref for detailed quality metadata), status (enum: current,
             historical, estimated, invalidated), version, created_at,
             created_by.
           — The atomic spatial unit. Every spatial operation ultimately
             references one or more Locations. A Location is Earth-
             referenced (WGS84 latitude/longitude) with mandatory accuracy
             metadata (ASM-S003). Accuracy varies by source: GPS 3-5m,
             GNSS RTK 1-2cm, survey sub-mm, geocode 12m urban / 150m
             rural, network 50-100m.
           — Distinguished from DESIGN Geometry vertex: a Location is a
             position on Earth in geodetic coordinates; a DESIGN vertex is
             a point in an artifact's local coordinate system (cartesian,
             cylindrical, spherical). The domains do not overlap.
           — Cross-substrate: PHYSICAL PhysicalAsset (TERM-P017)
             location_ref → Location. TEMPORAL TransitionTime (TERM-T029)
             location_from, location_to → Location. KNOWLEDGE Observation
             (TERM-K019) location_ref → Location. Principle P4.

TERM-S003: Address
           A structured human-readable location reference that maps to one
           or more geographic Locations through geocoding.
           — Has: address_id (UUID), components[] ({component_type (enum:
             street_number, street_name, unit, floor, building, city,
             district, subdistrict, state_province, postal_code, country,
             po_box, intersection, landmark, custom), value (text)}),
             formatted_address (text — display-ready string per locale),
             formatting_locale (IETF BCP 47 language tag), addressing_
             system (enum: street_based, block_based_jp, descriptive,
             plus_code, what3words, makani_ae, eircode_ie, custom),
             country_code (ISO 3166-1 alpha-2), geocoded_location_ref
             (nullable — Location TERM-S002 ref, the selected geocoded
             position), geocoding_confidence (nullable — float64 0-1),
             geocoding_result_ref (nullable — GeocodingResult TERM-S020
             ref, full geocoding audit trail), resolution_status (enum:
             unresolved, resolved_exact, resolved_interpolated,
             resolved_centroid, resolved_approximate, ambiguous),
             standardized (boolean — whether address has been standardized
             against authoritative database), version, created_at,
             created_by.
           — The bridge between human spatial description and machine
             coordinates. "123 Main St, Springfield, IL 62701" is an
             Address; (39.7817, -89.6501) is its geocoded Location.
             Geocoding (Address → Location) is inherently ambiguous
             (ASM-S013, Property S8). Address stores the human-readable
             form; Location stores the machine-interpretable coordinates;
             GeocodingResult records the translation with all candidates.
           — ISO 19160 compliant. Supports multiple addressing systems
             (Property S8 — not all countries use street-based addressing).
             Japan uses block-based; What3Words divides Earth into 3m
             squares; Plus Codes provide open-standard alphanumeric
             encoding.
           — Cross-substrate: BUSINESS references Address for billing/
             shipping context (BUSINESS owns billing vs shipping
             distinction; SPATIAL owns geographic resolution). BUSINESS
             Reservation, Order, Invoice reference Address via cross-
             substrate ref. Principle P4.
```

### Category B — Geographic Features & Data

```
TERM-S004: SpatialGeometry
           A geographic shape on or near Earth's surface, represented in
           an Earth-referenced coordinate system.
           — Has: geometry_id (UUID), geometry_type (enum: point,
             linestring, polygon, multipoint, multilinestring,
             multipolygon, geometrycollection), coordinates (GeoJSON
             RFC 7946 compatible array — longitude first per GeoJSON
             spec, converted to lat/lon for display per CRS
             coordinate_order), crs_ref (CoordinateReferenceSystem
             TERM-S001 ref), bounding_box (computed — {min_lon, min_lat,
             max_lon, max_lat}), area_m2 (computed — for polygons, geodesic
             area on WGS84 ellipsoid), length_m (computed — for linestrings,
             geodesic length), centroid (computed — {latitude, longitude}),
             is_valid (boolean — OGC Simple Features validation: no self-
             intersections, correct ring orientation, valid topology),
             validation_errors[] (text — if is_valid is false),
             version, created_at, created_by.
           — Distinguished from DESIGN Geometry (TERM-D006) per Principle
             P4. DESIGN Geometry = artifact shape (representation_type:
             brep, mesh, parametric; coordinate_system: cartesian,
             cylindrical, spherical, fractional_crystal, internal_
             molecular; scale: angstrom to km). SpatialGeometry =
             geographic shape (geometry_type: point, polygon, linestring;
             coordinate_system: WGS84, UTM, projected; scale: cm to Mm).
             DESIGN's coordinate_system enum has ZERO overlap with
             SPATIAL's CRS. The boundary is unambiguous.
           — For BIM integration: a building has BOTH a DESIGN Geometry
             (its IFC architectural form in local coordinates) AND a
             SPATIAL SpatialGeometry (its site footprint on the cadastral
             map in Earth-referenced coordinates). Two entities linked via
             the building's entity_id, stored in different substrates.
           — GeoJSON RFC 7946 compatibility: coordinates are stored in
             [longitude, latitude, altitude] order per GeoJSON spec.
             Display order (lat/lon vs lon/lat) depends on CRS
             coordinate_order. This is a known source of errors (Property
             S2) — the spec enforces GeoJSON storage order and explicit
             CRS for display.

TERM-S005: SpatialFeature
           A named real-world entity with geographic extent, typed
           properties, and temporal validity.
           — Has: feature_id (UUID), feature_type (enum: building,
             road_segment, parcel, water_body, utility_segment, poi,
             administrative_area, natural_feature, infrastructure, vehicle,
             person_location, transit_stop, parking, bridge, tunnel,
             custom), name (nullable — text), geometry_ref (SpatialGeometry
             TERM-S004 ref), properties ({key: {value, value_type (enum:
             text, integer, float, boolean, datetime, enum, ref)}}),
             temporal_validity ({valid_from: datetime, valid_to: nullable
             datetime — null means currently valid}), source_ref (text —
             provenance: OSM way ID, cadastral reference, survey number),
             accuracy_ref (SpatialAccuracy TERM-S029 ref), layer_ref
             (nullable — Layer TERM-S006 ref), version (integer — monotonic,
             incremented on each modification), status (enum: draft,
             active, archived, superseded), created_at, created_by,
             modified_at, modified_by.
           — The universal pattern beneath every GIS "feature," every
             OSM "element" (node/way/relation), every cadastral "parcel,"
             every POI entry, every fleet vehicle position. SpatialFeature
             is to SPATIAL what Entity (TERM-001) is to BUSINESS — the
             fundamental unit of geographic identity.
           — Temporal_validity distinguishes currently-accurate
             representations from historical ones. A building demolished
             in 2024 has valid_to: 2024-MM-DD. Road segments, parcel
             boundaries, and administrative areas all change over time.
             Property S7 (silent degradation) — spatial features must
             carry validity metadata because the map drifts from reality.
           — State machine: SM-S001 (draft → active → archived |
             superseded). Superseded when a new version of the same
             real-world entity is created with updated geometry or
             properties.

TERM-S006: Layer
           A thematic collection of SpatialFeatures sharing a common
           schema and purpose.
           — Has: layer_id (UUID), name, description, feature_schema
             ({attribute_name: {type, required, description, constraints}}
             — defines the property schema for all features in this layer),
             crs_ref (CoordinateReferenceSystem TERM-S001 ref — display
             CRS; features stored in WGS84), spatial_extent ({min_lon,
             min_lat, max_lon, max_lat} — bounding box of all features),
             temporal_extent ({valid_from, valid_to}), source_ref (text —
             data provider or authority), update_frequency (enum: static,
             daily, weekly, monthly, real_time, on_change), feature_count
             (integer — computed), dataset_ref (SpatialDataset TERM-S007
             ref), access_policy_ref (SpatialPolicy TERM-S028 ref),
             version, created_at, created_by.
           — Pattern beneath every GIS "layer," "theme," "overlay,"
             "feature class," OGC "feature type." Enables spatial
             composition — overlaying a transportation layer on a parcels
             layer on a terrain layer to produce an integrated spatial
             view.
           — Feature_schema enforces consistency: all buildings in a
             buildings layer share the same property schema (height,
             use_type, year_built). This is the spatial equivalent of a
             database table schema — features are rows, properties are
             columns, and the layer defines the schema.

TERM-S007: SpatialDataset
           A versioned, bounded collection of Layers constituting a
           coherent spatial view at a point in time.
           — Has: dataset_id (UUID), version (integer — monotonic,
             immutable once published), name, description, layers[]
             (Layer TERM-S006 refs), crs_ref (CoordinateReferenceSystem
             TERM-S001 ref), spatial_extent ({min_lon, min_lat, max_lon,
             max_lat}), temporal_extent ({valid_from, valid_to}),
             provenance ({source_authority, collection_method,
             processing_history[]}), quality_metadata ({completeness_pct,
             positional_accuracy_m, attribute_accuracy_pct, logical_
             consistency_pct — ISO 19157 quality elements}),
             comparison_baseline_ref (nullable — prior SpatialDataset
             version ref for diff analysis), status (enum: draft,
             published, superseded, archived), published_at, created_at,
             created_by.
           — Analogous to TEMPORAL Timeline (TERM-T011) — a SpatialDataset
             at version N is an immutable spatial snapshot. Enables "what
             changed" analysis: compare version N to version N-1 to
             identify new features, modified features, and removed
             features. Critical for cadastral updates, road network
             maintenance, and environmental monitoring.
           — ISO 19115 metadata compliant. Quality metadata per ISO 19157.
             Provenance tracks how the dataset was created, from what
             sources, through what processing chain.

TERM-S008: Raster
           A grid of cells covering a geographic area where each cell
           holds one or more numeric values representing a continuous
           field.
           — Has: raster_id (UUID), name, bounds (SpatialGeometry
             TERM-S004 polygon ref — the geographic extent), crs_ref
             (CoordinateReferenceSystem TERM-S001 ref), resolution
             ({cell_width, cell_height} — in CRS units), bands[]
             ({band_name, data_type (enum: uint8, int16, uint16, int32,
             float32, float64), nodata_value, statistics ({min, max, mean,
             stddev}), description}), rows (integer), columns (integer),
             compression (enum: none, deflate, lzw, zstd, jpeg, webp),
             tile_scheme (nullable — for tiled rasters: {tile_width,
             tile_height, origin}), source_ref, temporal_validity
             ({valid_from, valid_to}), accuracy_ref (SpatialAccuracy
             TERM-S029 ref), version, created_at, created_by.
           — Distinguished from SpatialGeometry (vector — discrete
             geographic objects with sharp boundaries) — Raster represents
             continuous field data (elevation surfaces, temperature
             distributions, rainfall intensity, land cover classification,
             population density heatmaps).
           — Pattern beneath every satellite image, digital elevation
             model (SRTM, ASTER GDEM, LIDAR DEM), weather radar product,
             land cover classification (NLCD, Corine), and spatial
             heatmap. DEM is a Raster with one band (elevation_m). A
             satellite image is a Raster with multiple bands (red, green,
             blue, near-infrared).
```

### Category C — Spatial Relationships & Topology

```
TERM-S009: SpatialRelationship
           A typed topological or metric relationship between two spatial
           entities (SpatialFeatures or SpatialGeometries).
           — Has: relationship_id (UUID), source_ref (SpatialGeometry or
             SpatialFeature ref), target_ref (SpatialGeometry or
             SpatialFeature ref), relationship_type (enum — topological:
             contains, within, intersects, overlaps, touches, crosses,
             disjoint, equals, covers, covered_by; metric: within_distance,
             nearest_k), computed_distance (nullable — float64, meters,
             for metric types), distance_metric (nullable — enum:
             euclidean, geodesic, network — for metric types), confidence
             (float64 0-1 — derived from source/target accuracy),
             computed_at (datetime), valid_until (nullable — when
             underlying features may have changed), version, created_at.
           — Topological types implement DE-9IM (Dimensionally Extended
             9-Intersection Model, Clementini et al. 1993) as standardized
             by OGC Simple Features. These are the spatial analog of
             Allen's interval algebra for TEMPORAL — the foundational
             spatial relationship calculus. Property S6 (topology vs
             metric duality).
           — Metric types compute distance using specified metric. Geodesic
             distance uses Vincenty or Karney formula on WGS84 ellipsoid.
             Network distance uses SpatialNetwork (TERM-S012) graph
             traversal. Euclidean distance is only valid for small areas
             where Earth curvature is negligible. Property S1 (Earth is
             not flat).

TERM-S010: SpatialConstraint
           A design-time rule constraining the spatial placement or
           relationship of entities.
           — Has: constraint_id (UUID), name, description, constraint_type
             (enum: must_be_within, must_not_overlap, minimum_distance,
             maximum_distance, adjacency_required, coverage_required,
             containment_required, exclusion_zone), hardness (enum: hard,
             soft, preference), violation_penalty (nullable — float64,
             cost of violating soft constraint, for optimization),
             target_features (SpatialFeature or SpatialGeometry refs —
             what is constrained), reference_geometry (SpatialGeometry
             TERM-S004 ref — the constraining region or boundary),
             parameters ({distance_m: float64, coverage_pct: float64,
             buffer_m: float64} — constraint-type-dependent), relaxation_
             priority (integer — order of relaxation when infeasible,
             lower = relax first), governing_ref (nullable — GOVERNANCE
             Norm or regulation ref for regulatory constraints),
             temporal_validity ({valid_from, valid_to}), version,
             created_at, created_by.
           — Analogous to TEMPORAL Constraint (TERM-T006). A zoning
             regulation ("no residential within 500m of industrial") is a
             SpatialConstraint with constraint_type: minimum_distance,
             hardness: hard, governing_ref → GOVERNANCE Norm. A delivery
             zone preference ("prefer locations within 15 min drive") is a
             SpatialConstraint with constraint_type: must_be_within,
             hardness: preference.
           — Distinguished from ProximityRule (TERM-S024): SpatialConstraint
             is a design-time rule evaluated during planning, configuration,
             and validation. ProximityRule is a runtime monitoring trigger
             evaluated continuously against live positions. SpatialConstraint
             = "this building must not be within 100m of the river"
             (checked at permit time). ProximityRule = "alert if this
             vehicle enters the restricted zone" (checked continuously).

TERM-S011: SpatialIndex
           A hierarchical spatial partitioning enabling efficient spatial
           queries at multiple resolutions.
           — Has: index_id (UUID), index_type (enum: h3, s2, quadtree,
             rtree, geohash), resolution (integer — level of detail;
             H3: 0-15, S2: 0-30, geohash: 1-12), coverage_area
             (SpatialGeometry TERM-S004 polygon ref — the area indexed),
             cell_count (computed — number of cells at this resolution),
             feature_count (computed — number of features indexed),
             created_at, created_by.
           — Exposes cell_id for any Location at any resolution. H3
             (Uber) divides Earth into hexagonal cells at 16 resolution
             levels (level 0: 4,357 km² avg area; level 15: 0.9 m²).
             S2 (Google) divides Earth into square cells on a cube
             projection at 31 levels. Geohash divides into rectangular
             cells at 12 levels (level 1: ~5000 km; level 12: ~3.7 cm).
           — Property S3 (scale spanning). The same SpatialIndex
             represents desk-scale (H3 level 15, ~1m²) through continental-
             scale (H3 level 3, ~12,393 km²) spatial queries. Multi-
             resolution is not an optimization — it is fundamental to
             spatial data access.
           — Enables: proximity queries ("what's within 500m"), spatial
             aggregation ("count features per H3 cell"), and efficient
             spatial joins. 73% of spatial queries are proximity-based
             (SRC-S016) — spatial indexing is the enabling infrastructure.
```

### Category D — Routing & Networks

```
TERM-S012: SpatialNetwork
           A graph of connected spatial segments enabling routing and flow
           analysis.
           — Has: network_id (UUID), name, network_type (enum: road,
             transit, pedestrian, cycling, utility_electric, utility_water,
             utility_gas, utility_telecom, flight, maritime, rail,
             multimodal), nodes[] (Location TERM-S002 refs — intersection
             points and endpoints), edges[] (NetworkSegment TERM-S013
             refs), directionality (enum: directed, undirected, mixed),
             connectivity_rules ({allow_u_turns: boolean, turn_restrictions
             [] ({from_segment_ref, to_segment_ref, restriction_type:
             enum: no_left_turn, no_right_turn, no_u_turn, only_straight,
             time_restricted})}), temporal_validity ({valid_from,
             valid_to}), coverage_area (SpatialGeometry TERM-S004 polygon
             ref), statistics ({total_length_km, node_count, edge_count,
             avg_connectivity}), version, created_at, created_by.
           — Pattern beneath every road network (OSM ways + nodes), transit
             network (GTFS stops + routes), utility network (pipes/cables
             + junctions), airline route network (airports + routes), and
             maritime shipping network (ports + sea lanes).
           — Network_type determines routing behavior: road networks have
             turn restrictions and speed limits; transit networks have
             schedules and transfer penalties; utility networks have flow
             capacity and pressure constraints; pedestrian networks allow
             bidirectional traversal of one-way streets.

TERM-S013: NetworkSegment
           A single traversable edge in a SpatialNetwork with travel
           characteristics.
           — Has: segment_id (UUID), network_ref (SpatialNetwork TERM-S012
             ref), geometry_ref (SpatialGeometry TERM-S004 ref — linestring),
             from_node (Location TERM-S002 ref), to_node (Location
             TERM-S002 ref), length_m (float64 — geodesic length),
             typical_travel_time_s (float64 — average traversal time),
             capacity (nullable — integer, vehicles/hour for roads,
             passengers/hour for transit), speed_limit_ms (nullable —
             float64, meters/second), access_restrictions[] ({vehicle_type
             (enum: car, truck, bus, motorcycle, bicycle, pedestrian,
             emergency), time_restriction (nullable — TimeWindow ref),
             permit_required (boolean)}), cost (nullable — float64 —
             toll, fare, fuel cost), bidirectional (boolean), condition
             (enum: open, restricted, closed, planned, under_construction),
             road_class (nullable — enum: motorway, trunk, primary,
             secondary, tertiary, residential, service, track, path),
             surface (nullable — enum: paved, unpaved, gravel, dirt),
             temporal_validity ({valid_from, valid_to}), version,
             created_at, created_by.
           — The atomic routing unit. What TEMPORAL's TransitionTime
             (TERM-T029) needs to compute travel duration: a sequence of
             NetworkSegments from A to B yields total distance and
             estimated travel time.
           — Distinguished from SpatialFeature (TERM-S005) of type
             road_segment: SpatialFeature captures the geographic entity
             (a road exists here with these properties). NetworkSegment
             captures the routing graph edge (you can travel from node A
             to node B along this path in this time at this cost with
             these restrictions). The same physical road may correspond
             to one SpatialFeature and multiple NetworkSegments (one per
             direction, one per lane configuration).

TERM-S014: Route
           An ordered sequence of NetworkSegments from origin to
           destination with travel metrics.
           — Has: route_id (UUID), origin (Location TERM-S002 ref),
             destination (Location TERM-S002 ref), waypoints[] (Location
             TERM-S002 refs — ordered intermediate stops), segments[]
             (NetworkSegment TERM-S013 refs — ordered traversal sequence),
             total_distance_m (float64), estimated_duration_s (float64),
             optimization_criterion (enum: shortest, fastest, cheapest,
             fewest_turns, most_scenic, avoid_tolls, avoid_highways,
             avoid_ferries, truck_safe), alternatives[] (Route refs —
             alternative route options), traffic_model (enum: none,
             historical, live, predictive), vehicle_profile (nullable —
             {height_m, width_m, length_m, weight_kg, axle_count,
             fuel_type, hazmat_class}), computed_at (datetime UTC),
             validity_window ({valid_from, valid_to} — temporal range
             during which this route is expected to remain valid),
             status (enum: computed, active, invalidated, completed),
             accuracy_ref (SpatialAccuracy TERM-S029 ref — derived from
             underlying network data quality), version, created_at.
           — State machine: SM-S002 (computed → active → completed |
             invalidated). A Route is invalidated when SpatialChange
             (TERM-S030) affects any of its segments. Invalidation
             triggers recomputation notification.
           — What TEMPORAL's TransitionTime.travel_duration_model defers
             to SPATIAL. SPATIAL computes "3.2 km, 12 min driving via
             Main St → Oak Ave → Highway 101"; TEMPORAL consumes the 12
             minutes for scheduling. Protocol defined in INT-S001.
           — Cross-substrate: TEMPORAL consumes Route.estimated_duration_s
             for TransitionTime (INT-S001). BUSINESS consumes Route.
             total_distance_m for logistics cost computation (INT-S003).

TERM-S015: ServiceArea
           The geographic extent reachable from a Location within given
           constraints — a computed output, not a declared input.
           — Has: service_area_id (UUID), origin (Location TERM-S002 ref),
             constraint_type (enum: isochrone, isodistance, isocost),
             constraint_value (float64 — minutes for isochrone, meters
             for isodistance, currency for isocost), network_ref
             (SpatialNetwork TERM-S012 ref), vehicle_profile (nullable —
             same as Route), resulting_geometry (SpatialGeometry TERM-S004
             polygon ref — the computed reachable area), contour_intervals
             [] (nullable — multiple thresholds: {value, geometry_ref}
             for graduated service areas, e.g., 5min/10min/15min rings),
             resolution (enum: high, medium, low — computation detail
             level), computed_at (datetime), validity_window ({valid_from,
             valid_to}), version, created_at.
           — Pattern beneath every delivery radius, ambulance response
             zone (8-minute isochrone per NFPA 1710), transit accessibility
             map (30-minute isochrone from station), commute shed, store
             catchment area.
           — Distinguished from Zone (TERM-S016) and Territory (TERM-S017):
             Zone = declared by authority (input, policy-defined).
             Territory = assigned to agent (input, assignment-defined).
             ServiceArea = computed from constraints (output, reachability-
             derived). Three genuinely different cognitive operations: a
             zoning board draws a Zone; a manager assigns a Territory; a
             routing engine computes a ServiceArea.
```

### Category E — Zones, Territories & Boundaries

```
TERM-S016: Zone
           A named geographic region with associated rules and policies,
           declared by an authority.
           — Has: zone_id (UUID), name, zone_type (enum: administrative,
             zoning_land_use, delivery, service_coverage, regulatory,
             environmental, restricted, hazard, military, maritime,
             airspace, school_district, fire_district, census_tract,
             custom), geometry_ref (SpatialGeometry TERM-S004 polygon
             ref), rules[] (SpatialConstraint TERM-S010 refs or
             cross-substrate refs to GOVERNANCE Norm), governing_
             authority_ref (nullable — GOVERNANCE Authority ref),
             temporal_validity ({valid_from, valid_to}), hierarchy_
             parent_ref (nullable — Zone ref, for nested zones: city
             within county within state within country), hierarchy_level
             (integer — 0 = top level), population (nullable — integer),
             metadata ({key: value} — zone-specific attributes),
             status (enum: proposed, active, suspended, dissolved),
             version, created_at, created_by.
           — State machine: SM-S003 (proposed → active → suspended |
             dissolved). Zones can be suspended (temporarily inactive)
             or dissolved (permanently ended with valid_to date).
           — Distinguished from PHYSICAL Zone (TERM-P018) per Principle
             P4: PHYSICAL Zone = operational safety/security grouping
             within a facility (IEC 62443 zones, hazardous areas per
             IEC 60079, sensor/actuator scope). SPATIAL Zone = geographic
             region with associated policies (city-scale and above,
             administrative boundaries, land-use zones, delivery areas).
             PHYSICAL Zone MAY reference SPATIAL Zone for the geographic
             position of the facility containing it.
           — Zone type determines governance integration: administrative
             zones link to GOVERNANCE Jurisdiction (INT-S005);
             zoning_land_use zones link to GOVERNANCE Norm for permitted
             activities; regulatory zones link to GOVERNANCE compliance
             requirements; hazard zones link to PHYSICAL safety procedures.

TERM-S017: Territory
           An assigned geographic scope of responsibility for an agent or
           team, with performance metrics and rebalancing rules.
           — Has: territory_id (UUID), name, assignee_ref (text — agent,
             team, or organizational unit reference), geometry_ref
             (SpatialGeometry TERM-S004 polygon ref), assignment_criteria
             (enum: balanced_workload, geographic_contiguity,
             population_based, revenue_based, demand_based, custom),
             performance_metrics[] ({metric_name, target_value,
             current_value, unit} — e.g., coverage_percentage: 95%,
             avg_response_time_min: 12, utilization_pct: 78),
             rebalancing_trigger ({trigger_type (enum: threshold_breach,
             periodic, manual, demand_shift), threshold (nullable),
             evaluation_frequency (nullable)}), rebalancing_constraints
             ({minimize_disruption: boolean, maintain_contiguity: boolean,
             max_reassignment_pct: float64, min_territory_area_m2:
             nullable float64}), zone_ref (nullable — parent Zone ref,
             if territory exists within a zone), status (enum: proposed,
             active, under_review, dissolved), version, created_at,
             created_by.
           — State machine: SM-S005 (proposed → active → under_review →
             active | dissolved). Under_review when rebalancing_trigger
             fires; returns to active after rebalancing or manual
             confirmation.
           — Pattern beneath every sales territory, patrol zone, delivery
             driver area, census tract assignment, school district
             attendance zone, field service coverage area.
           — Distinct from Zone: Zone has rules (what is permitted/
             required here); Territory has assignment and performance
             (who is responsible here and how well are they covering it).
             A delivery Zone defines the service area; a delivery Territory
             assigns a specific driver to a portion of that zone with
             performance targets.

TERM-S018: Boundary
           A dividing line between Zones or Territories with permeability
           rules governing crossing.
           — Has: boundary_id (UUID), geometry_ref (SpatialGeometry
             TERM-S004 linestring ref), left_zone_ref (nullable — Zone
             TERM-S016 ref), right_zone_ref (nullable — Zone TERM-S016
             ref), left_territory_ref (nullable — Territory TERM-S017
             ref), right_territory_ref (nullable — Territory TERM-S017
             ref), crossing_rules (enum: open, restricted, closed,
             scheduled, permit_required), transition_requirements[]
             ({requirement_type (enum: customs, inspection, toll,
             checkpoint, vaccination, visa, quarantine), description,
             processing_time_s (nullable)}), disputed (boolean),
             dispute_parties[] (nullable — text array of claiming
             entities), dispute_description (nullable — text),
             temporal_validity ({valid_from, valid_to}), version,
             created_at, created_by.
           — Pattern beneath every international border, state/province
             boundary, property line, zoning boundary, fence line,
             administrative district boundary.
           — UNK-S005 (sovereignty disputes) addressed by disputed flag
             and dispute_parties[]. Multiple boundary claims for the same
             geographic line are stored as separate Boundary entities.
             Display selection depends on user jurisdiction and
             organizational policy — the spec does not assert which
             boundary is "correct" for disputed territories.
```

### Category F — Places, Geocoding & Movement

```
TERM-S019: Place
           A named location with cultural, social, or functional
           significance beyond mere coordinates.
           — Has: place_id (UUID), name ({primary_name: text, language:
             BCP 47 tag}), alternate_names[] ({name: text, language:
             BCP 47 tag, name_type (enum: official, colloquial,
             historical, abbreviated, transliterated)}), place_type
             (enum: continent, country, sovereign_state, state_province,
             county, city, town, village, neighborhood, district,
             landmark, poi, campus, airport, port, station, park,
             custom), geometry_ref (SpatialGeometry TERM-S004 ref —
             point for POIs, polygon for areas), address_ref (nullable —
             Address TERM-S003 ref), aliases[] (text — informal names),
             hierarchy ({parent_place_ref: nullable Place ref,
             hierarchy_path: text — "Earth/North America/United States/
             Illinois/Springfield"}), population (nullable — integer),
             timezone_ref (nullable — TEMPORAL CalendarSystem TERM-T027
             ref for timezone association), elevation_m (nullable),
             metadata ({key: value} — place-specific attributes: opening
             hours, rating, website, phone), source_ref, version,
             created_at, created_by.
           — Pattern beneath every gazetteer entry, Google Places record,
             OSM named place, Foursquare venue, Geonames entry, Wikipedia
             geographic article. Place is semantically richer than
             Location (a point) or SpatialFeature (a geographic entity) —
             it carries cultural meaning, multilingual naming, and
             hierarchical geographic context.
           — Hierarchy enables "Springfield, Illinois, United States"
             disambiguation — the same place name at different hierarchy
             levels resolves ambiguity (Property S8). Place.hierarchy is
             a geographic gazetteer; Address.components is a postal
             routing structure. They intersect but are not identical.

TERM-S020: GeocodingResult
           The output of translating between human spatial description
           and machine coordinates, with full ambiguity exposure.
           — Has: geocoding_result_id (UUID), input ({text: text,
             input_type (enum: address_text, structured_address,
             coordinates, place_name, plus_code, what3words)}),
             result_type (enum: forward, reverse), candidates[]
             ({candidate_idx: integer, location_ref: Location TERM-S002
             ref, formatted_address: text, match_type (enum: exact,
             interpolated, centroid, approximate, intersection),
             confidence (float64 0-1), components_matched[] (text —
             which input components contributed to match), source (text —
             which geocoding database matched)}), selected_candidate_idx
             (nullable — integer, which candidate was chosen),
             selection_method (nullable — enum: highest_confidence,
             user_selected, policy_default, ai_agent_selected),
             ambiguity_flag (boolean — true if multiple candidates with
             confidence > 0.5), processing_time_ms (integer), computed_at
             (datetime), computed_by (text — actor ref).
           — State machine: SM-S004 (pending → resolved | ambiguous |
             failed). Resolved when a candidate is selected. Ambiguous
             when multiple high-confidence candidates exist and no
             selection has been made. Failed when no candidates match.
           — Property S8 (geocoding ambiguity). Every geocoding operation
             produces a GeocodingResult with ranked candidates. "123 Main
             St" → [{Springfield IL, confidence: 0.92}, {Springfield MO,
             confidence: 0.88}, {Springfield MA, confidence: 0.85}, ...].
             The selected candidate is an explicit choice recorded in the
             audit trail, not a silent assumption.

TERM-S021: Trajectory
           A time-ordered sequence of Locations representing movement
           through geographic space.
           — Has: trajectory_id (UUID), entity_ref (text — person, vehicle,
             asset reference; may link to PHYSICAL PhysicalAsset
             TERM-P017 or TEMPORAL SchedulableResource TERM-T016),
             positions[] ({location_ref: Location TERM-S002 ref,
             timestamp: datetime UTC, speed_ms: nullable float64,
             heading_degrees: nullable float64, accuracy_m: float64}),
             transport_mode (enum: walking, driving, transit, cycling,
             flight, maritime, rail, unknown), dwell_points[] ({location_
             ref: Location TERM-S002 ref, arrival_time: datetime,
             departure_time: datetime, dwell_duration_s: float64} —
             locations where entity stopped for > dwell_threshold),
             dwell_threshold_s (float64 — minimum stop duration to
             qualify as dwell point), total_distance_m (float64 —
             computed), start_time (datetime), end_time (nullable —
             datetime, null for active trajectories), simplification_
             algorithm (nullable — enum: douglas_peucker, visvalingam,
             radial_distance — if trajectory has been simplified),
             status (enum: active, completed, archived), version,
             created_at.
           — Pattern beneath every fleet GPS trace, delivery tracking
             breadcrumb, person movement log, animal migration track,
             vessel AIS track, aircraft ADS-B track.
           — Bridges SPATIAL and TEMPORAL — a trajectory is both spatial
             (geographic path) and temporal (timestamped positions). Owned
             by SPATIAL because the primary dimension is geographic path;
             TEMPORAL references for duration computation and schedule
             adherence.
           — Privacy-sensitive: Trajectory data reveals movement patterns,
             visited locations, daily routines. Subject to SpatialPolicy
             privacy rules (ASM-S010). Trajectory data may be simplified
             (fewer points), temporally cloaked (fuzzy timestamps), or
             spatially cloaked (degraded precision) per policy.
```

### Category G — Coverage & Proximity

```
TERM-S022: Coverage
           The degree to which a resource or service covers a geographic
           area, with gap identification.
           — Has: coverage_id (UUID), name, resource_type (text — what is
             providing coverage: fire stations, cell towers, retail stores,
             delivery drivers, hospitals), service_type (text — what
             service is being covered: emergency response, cellular signal,
             retail access, delivery, healthcare), target_area_ref
             (SpatialGeometry TERM-S004 polygon ref — the area that should
             be covered), covered_area_ref (SpatialGeometry TERM-S004
             polygon ref — the area actually covered), coverage_percentage
             (float64 0-100), gap_areas[] (SpatialGeometry TERM-S004
             polygon refs — uncovered regions), overlap_areas[] (nullable —
             SpatialGeometry refs — regions with redundant coverage),
             coverage_standard_ref (nullable — text, regulatory minimum:
             "NFPA 1710: 8-minute response time for 90% of calls"),
             meets_standard (nullable — boolean), computation_method
             (text — how coverage was computed: service_area_union,
             buffer_union, signal_propagation_model, custom),
             computed_at (datetime), validity_window ({valid_from,
             valid_to}), version, created_at.
           — Pattern beneath cell tower coverage maps, fire station
             response zones, delivery service coverage, broadband access
             maps, healthcare facility catchment, retail market coverage.
           — Coverage gap identification is the primary analytical value:
             "where are we NOT covering?" drives resource allocation
             decisions (new fire station placement, new cell tower sites,
             delivery expansion planning).

TERM-S023: Density
           Spatial distribution metric of features or values over a
           geographic area.
           — Has: density_id (UUID), name, feature_type (text — what is
             being counted: population, crimes, POIs, traffic incidents,
             delivery demand), area_ref (SpatialGeometry TERM-S004
             polygon ref — analysis area), value_type (enum: count,
             intensity, weighted), resolution ({cell_size_m: float64} or
             {h3_resolution: integer}), computation_method (enum: kernel_
             density_estimation, grid_count, voronoi, hexbin, custom),
             kernel_bandwidth_m (nullable — for KDE), result_ref
             (nullable — Raster TERM-S008 ref for gridded output or
             SpatialDataset TERM-S007 ref for vector output), units
             (text — "persons/km²", "incidents/month/hex"), statistics
             ({min, max, mean, stddev, total}), computed_at (datetime),
             version, created_at.
           — Pattern beneath population density maps, crime heatmaps,
             demand density for logistics, traffic density, land use
             intensity, point-of-interest concentration.
           — Stored as Raster (gridded surface) or vector (zone-based
             aggregation). Density is the semantic wrapper that records
             what was measured, how, and with what method. The underlying
             data is a Raster or SpatialDataset; Density adds analytical
             context.

TERM-S024: ProximityRule
           A runtime distance-based monitoring rule with trigger semantics,
           evaluated continuously against live positions.
           — Has: proximity_rule_id (UUID), name, source_entity_ref (text —
             what is being monitored: vehicle, person, asset),
             target_geometry_ref (SpatialGeometry TERM-S004 ref — the
             reference area: geofence polygon, exclusion zone, POI
             buffer), distance_threshold_m (float64), distance_metric
             (enum: euclidean, geodesic, network, travel_time),
             direction (enum: enter, exit, both, approach, depart),
             trigger_action (enum: alert, block, log, escalate,
             notify_external), trigger_payload ({notification_channel,
             escalation_ref, custom_data}), monitoring_frequency (enum:
             continuous, interval_seconds, on_position_update),
             active_window (nullable — TEMPORAL TimeWindow ref — when
             this rule is active), cooldown_s (nullable — minimum time
             between repeated triggers), status (enum: active, paused,
             expired), last_triggered_at (nullable — datetime),
             trigger_count (integer), version, created_at, created_by.
           — Distinguished from SpatialConstraint (TERM-S010):
             SpatialConstraint is a design-time rule evaluated during
             planning, configuration, and validation ("this building must
             not be within 100m of the river"). ProximityRule is a runtime
             monitoring trigger evaluated continuously against live
             positions ("alert if this vehicle enters the restricted
             zone"). Different lifecycle, different evaluation frequency,
             different actors.
           — Pattern beneath every geofence, buffer zone monitoring,
             exclusion zone enforcement (court-ordered, military),
             proximity alert (fleet approaching customer), delivery
             radius trigger, and safety perimeter monitoring.
```

### Category H — Indoor Spatial

```
TERM-S025: Floor
           A vertical spatial layer within a building or structure,
           bridging outdoor and indoor spatial domains.
           — Has: floor_id (UUID), building_ref (SpatialFeature TERM-S005
             ref — the building this floor belongs to), level_number
             (integer — 0 = ground level, positive = above ground,
             negative = below ground), elevation_m (float64 — floor
             elevation above ground datum), geometry_ref (SpatialGeometry
             TERM-S004 polygon ref — floor footprint), name (text —
             display name: "Ground Floor", "Basement 1", "Level 3"),
             ceiling_height_m (float64), gross_area_m2 (computed from
             geometry), usable_area_m2 (nullable — excludes walls,
             shafts, structural elements), indoor_spaces[] (IndoorSpace
             TERM-S026 refs), vertical_connections[] ({connection_type
             (enum: stairs, elevator, escalator, ramp), connects_to_floor
             _ref: Floor ref, location_ref: Location TERM-S002 ref}),
             version, created_at, created_by.
           — The fundamental indoor/outdoor discontinuity primitive
             (Property S4). GPS does not work indoors. Floor plans replace
             road networks. Vertical movement (stairs, elevators) replaces
             horizontal road routing. A journey from parking lot (outdoor,
             GPS) to meeting room (indoor, floor 3) crosses this boundary
             twice.
           — Vertical_connections enable indoor routing across floors:
             stairs from Floor 1 to Floor 2, elevator from Floor -1 to
             Floor 10. These connections become edges in an indoor routing
             graph, complementing corridor adjacency within each floor.

TERM-S026: IndoorSpace
           A navigable or occupiable space within a Floor, with
           connectivity for indoor routing.
           — Has: indoor_space_id (UUID), floor_ref (Floor TERM-S025 ref),
             space_type (enum: room, corridor, stairwell, elevator_shaft,
             escalator, open_area, lobby, restroom, utility_room,
             server_room, conference_room, office, lab, warehouse_aisle,
             custom), name (text — "Room 301", "Main Corridor", "Elevator
             A"), geometry_ref (SpatialGeometry TERM-S004 polygon ref —
             within floor footprint), capacity (nullable — integer,
             maximum occupancy), current_occupancy (nullable — integer,
             from sensors), accessibility_features[] (enum: wheelchair_
             accessible, hearing_loop, braille_signage, automatic_door,
             tactile_floor), connected_spaces[] ({space_ref: IndoorSpace
             ref, connection_type (enum: door, open, restricted, emergency
             _only), traversal_time_s: float64}), schedulable_resource_ref
             (nullable — TEMPORAL SchedulableResource TERM-T016 ref — for
             bookable rooms), amenities[] (text — projector, whiteboard,
             video_conferencing, kitchen), sensor_refs[] (nullable —
             PHYSICAL Sensor TERM-P001 refs for occupancy/environment),
             version, created_at, created_by.
           — Pattern beneath every indoor positioning system, building
             wayfinding app, room booking system, evacuation plan,
             hospital ward navigation, airport terminal navigation,
             warehouse aisle routing.
           — Connected_spaces[] forms the indoor routing graph: Room 301
             connects to Corridor 3A via door; Corridor 3A connects to
             Stairwell B via open connection; Stairwell B connects to
             Floor 2 Corridor via stairs (vertical connection on Floor).
             Indoor routing = graph traversal of connected_spaces within
             and across Floors.
           — Cross-substrate: TEMPORAL SchedulableResource ref enables
             room booking integration — "Conference Room 3A" is both a
             SPATIAL IndoorSpace (navigable, with capacity and amenities)
             and a TEMPORAL SchedulableResource (bookable, with
             availability and conflicts). One physical room, two
             substrate perspectives. Principle P4.
```

### Category I — Spatial Authority, Policy & Quality

```
TERM-S027: SpatialEnvelope
           Bounded AI Agent authority over spatial operations, scoping
           what an agent can do geographically.
           — Has: envelope_id (UUID), agent_ref (text — AI agent
             identifier), max_geographic_scope ({scope_type (enum:
             bounding_box, zone_ref, global), bounding_box: nullable
             {min_lat, min_lon, max_lat, max_lon}, zone_ref: nullable
             Zone TERM-S016 ref}), accessible_spatial_datasets[]
             (SpatialDataset TERM-S007 refs), geocoding_authority
             ({can_create: boolean, can_modify: boolean, can_select_
             candidate: boolean}), routing_authority ({can_compute:
             boolean, can_cache: boolean, max_route_distance_m: nullable
             float64}), zone_modification_authority ({can_create: boolean,
             can_modify_boundary: boolean, can_modify_rules: boolean,
             zone_types_permitted[] (enum subset)}), feature_creation_
             authority ({can_create: boolean, can_modify: boolean,
             feature_types_permitted[] (enum subset)}), territory_
             assignment_authority ({can_assign: boolean, can_rebalance:
             boolean, max_territories: nullable integer}), spatial_
             accuracy_threshold (float64 — minimum acceptable accuracy_m
             for agent decisions; agent must not act on data less accurate
             than this), override_limit (integer — max spatial operations
             per period without human review), version, created_at,
             created_by.
           — Sits in the Agent authority chain between TemporalEnvelope
             and DesignEnvelope: Business → Governance → Epistemic →
             Temporal → **Spatial** → Design → Compute → Communicative →
             Physical. An agent must know when it can act (Temporal)
             before determining where it can act (Spatial). Spatial
             authority is a geographic-scoping step.
           — Envelope violations are blocked and logged. An agent with
             max_geographic_scope: Europe cannot compute routes in Asia.
             An agent without zone_modification_authority cannot modify
             Zone boundaries regardless of its role-based permissions.

TERM-S028: SpatialPolicy
           A declarative rule constraining spatial operations, applied
           per actor and context.
           — Has: policy_id (UUID), name, policy_type (enum: access,
             quality, retention, privacy, compliance, resolution),
             scope ({applies_to_actors[] (ACT-S### refs), applies_to_
             datasets[] (SpatialDataset refs), applies_to_zones[]
             (Zone refs)}), rules (type-dependent):
             — access: {visibility_level (enum: full, filtered, degraded,
               none), feature_types_visible[], layers_visible[]}
             — quality: {min_accuracy_m: float64, min_confidence: float64,
               require_accuracy_metadata: boolean}
             — retention: {retention_period ({value, unit}), archive_
               after ({value, unit}), delete_after (nullable {value,
               unit})}
             — privacy: {k_anonymity_k (integer — minimum entities in
               any spatial group), spatial_cloaking_radius_m (float64 —
               minimum imprecision added to locations), temporal_cloaking_
               window_s (integer — minimum time uncertainty added to
               timestamps), differential_privacy_epsilon (nullable —
               float64), precision_level (enum: exact, building, block,
               neighborhood, city, region, country)}
             — compliance: {data_residency_zones[] (Zone refs — spatial
               data must be stored within these zones), cross_border_
               transfer_permitted (boolean), regulatory_refs[] (text —
               GDPR, CCPA, HIPAA, COPPA, etc.)}
             — resolution: {max_precision_level (enum: exact, building,
               block, neighborhood, city, region, country) — maximum
               coordinate precision exposed to actor}
           , enforcement (enum: hard_block, soft_warn, log_only),
             temporal_validity ({valid_from, valid_to}), version,
             created_at, created_by.
           — Privacy type implements the analog of TEMPORAL's busy/free
             visibility (TRUST-T004) for spatial data: just as TEMPORAL
             can show "busy" without showing meeting details, SPATIAL can
             show "neighborhood" without showing exact coordinates.
             Precision degradation is irreversible at the API boundary.
           — Retention type implements differentiated retention per data
             sensitivity: cadastral 100+ years, road networks 10+ years,
             fleet positions 90 days, proximity rule triggers 30 days.
             Per ASM-S012.

TERM-S029: SpatialAccuracy
           Metadata about the positional quality of spatial data, mandatory
           on every spatial measurement.
           — Has: accuracy_id (UUID), horizontal_accuracy_m (float64 —
             CEP95: 95% of true positions within this radius),
             vertical_accuracy_m (nullable — float64, CEP95),
             temporal_accuracy ({measurement_age_s: float64 — time since
             measurement, staleness_threshold_s: float64 — when
             measurement is considered stale}), accuracy_method (enum:
             gps_single, gnss_rtk, gnss_ppp, survey_grade, lidar,
             photogrammetry, interpolation, estimation, geocode,
             digitized, derived), confidence_level (float64 0-1 — overall
             quality confidence), source_ref (text — measurement source
             identifier), knowledge_proposition_ref (nullable — KNOWLEDGE
             Proposition ref — when accuracy claim enters the epistemic
             record), degradation_rate (nullable — float64 m/year —
             estimated rate at which this spatial data diverges from
             reality, per Property S7), last_verified_at (nullable —
             datetime — when this accuracy was last field-verified),
             version, created_at.
           — Critical because spatial data degrades silently over time
             (Property S7). A geocoded address has 12m urban accuracy
             (SRC-S016). A GPS position has 3-5m accuracy. A survey-grade
             measurement has sub-mm accuracy. Every spatial decision's
             reliability depends on knowing this. ASM-S003.
           — Propagation: when spatial operations combine multiple inputs,
             the output accuracy is the worst of the inputs. A Route
             computed from GPS-grade Locations (±5m) has at least ±5m
             accuracy. A Coverage analysis built on geocoded positions
             (±12m) cannot claim survey-grade precision. Accuracy never
             silently improves through computation. SUCCESS-S003.
```

### Category J — Spatial Disruptions

```
TERM-S030: SpatialChange
           An event invalidating existing spatial assumptions, with
           cascade analysis identifying all affected downstream
           computations.
           — Has: change_id (UUID), change_type (enum: closure, demolition,
             rerouting, redistricting, reassignment, construction, flooding,
             earthquake, wildfire, landslide, infrastructure_failure,
             natural_disaster, planned_modification), description (text),
             affected_area (SpatialGeometry TERM-S004 polygon ref — the
             geographic extent of the change), affected_features[]
             (SpatialFeature TERM-S005 refs — features directly affected),
             affected_routes[] (Route TERM-S014 refs — routes passing
             through affected area, now potentially invalid), affected_
             zones[] (Zone TERM-S016 refs — zones with boundary or
             rule changes), affected_coverages[] (Coverage TERM-S022
             refs — coverage analyses to recompute), affected_service_
             areas[] (ServiceArea TERM-S015 refs — service areas
             potentially changed), cascade_analysis ({invalidated_routes_
             count: integer, invalidated_service_areas_count: integer,
             invalidated_coverages_count: integer, affected_territories
             _count: integer, estimated_recomputation_cost: text}),
             effective_datetime (datetime — when the change takes effect),
             duration_type (enum: permanent, temporary), end_datetime
             (nullable — for temporary changes), severity (enum: minor,
             moderate, major, critical), source_ref (text — who/what
             reported the change), verified (boolean — whether change has
             been field-verified), version, created_at, created_by.
           — Analogous to TEMPORAL Disruption (TERM-T013). When a road
             closes, all cached Routes through that segment become
             invalid; all ServiceAreas relying on that segment need
             recomputation; all Trajectories in progress may need
             rerouting; all Coverage analyses including that segment's
             capacity are stale. SPATIAL emits substrate.spatial.change
             .detected; downstream substrates consume and adapt.
           — Distinguished from SpatialFeature version update:
             SpatialChange is the EVENT with cascade analysis (what broke,
             what's invalidated, what needs recomputation). SpatialFeature
             version update is the resulting STATE change (road_segment
             status: closed). The event drives the cascade; the state
             change records the outcome.
           — Cross-substrate cascade: TEMPORAL creates Disruption when
             SpatialChange invalidates scheduled locations (room closed
             for renovation → meeting needs new room). BUSINESS
             replans deliveries when SpatialChange invalidates Routes.
             GOVERNANCE re-evaluates compliance when SpatialChange
             modifies Zone boundaries.
```

---

## 4. CORE CAPABILITIES (WHAT THE SYSTEM MUST DO)

> Capabilities use RFC 2119 language: MUST (required), SHOULD
> (recommended), MAY (optional). Each capability references the
> primitives it operates on and the actors who invoke it.

### Coordinate Reference & Location Management

```
CAP-S001: The system MUST support registration and management of
          CoordinateReferenceSystems (TERM-S001). The system MUST include
          WGS84 (EPSG:4326) as the default storage CRS. The system MUST
          support registration of additional CRS from the EPSG registry
          and custom local CRS. All coordinate storage MUST be in WGS84;
          display and computation MAY use any registered CRS with
          explicit transform.
          Actors: ACT-S002.

CAP-S002: The system MUST support coordinate transformation between any
          two registered CoordinateReferenceSystems. Transforms MUST
          preserve positional accuracy within the transform method's
          documented error bounds. The system MUST track transform
          accuracy: a transform from NAD83 to WGS84 introduces ~1-2m
          error; this error MUST be reflected in the output
          SpatialAccuracy. The system SHOULD warn when a requested
          projection distorts area or distance beyond a configurable
          threshold for the operation's purpose.
          Actors: ACT-S001, ACT-S002, ACT-S003, ACT-S004.

CAP-S003: The system MUST support creation, modification, and querying
          of Locations (TERM-S002). Every Location MUST carry accuracy
          metadata (ASM-S003). The system MUST validate latitude (-90 to
          +90) and longitude (-180 to +180) ranges. The system MUST
          support altitude (WGS84 ellipsoidal height). The system SHOULD
          support speed and heading for moving entities. The system MUST
          support indoor positions via floor_ref.
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S005, ACT-S006.

CAP-S004: The system MUST support creation, standardization, geocoding,
          and reverse geocoding of Addresses (TERM-S003). Geocoding
          (Address → Location) MUST always produce a GeocodingResult
          (TERM-S020) with ranked candidates and confidence scores —
          never a single point without ambiguity metadata. Reverse
          geocoding (Location → Address) MUST return the nearest Address
          with distance and confidence. The system MUST support multiple
          addressing systems (street_based, block_based_jp, plus_code,
          what3words, custom) per ASM-S013.
          Actors: ACT-S001, ACT-S002, ACT-S003, ACT-S004, ACT-S005.
```

### Spatial Feature & Data Management

```
CAP-S005: The system MUST support creation, modification, versioning,
          and lifecycle management of SpatialFeatures (TERM-S005).
          Features follow SM-S001 (draft → active → archived |
          superseded). The system MUST maintain version history for all
          features. The system MUST support temporal_validity for
          tracking when a feature representation is accurate. The system
          MUST support feature_type classification.
          Actors: ACT-S001, ACT-S002, ACT-S003, ACT-S004.

CAP-S006: The system MUST support creation and validation of
          SpatialGeometries (TERM-S004). The system MUST validate
          geometry per OGC Simple Features: no self-intersections for
          polygons, correct ring orientation (exterior counterclockwise,
          interior clockwise per GeoJSON), valid topology. The system
          MUST compute derived properties: bounding_box, area_m2 (for
          polygons, geodesic on WGS84), length_m (for linestrings,
          geodesic), centroid. The system MUST support all GeoJSON
          geometry types.
          Actors: ACT-S001, ACT-S002, ACT-S003, ACT-S004.

CAP-S007: The system MUST support creation and management of Layers
          (TERM-S006) with enforced feature schemas. The system MUST
          validate that SpatialFeatures added to a Layer conform to the
          Layer's feature_schema. The system MUST compute spatial_extent
          and feature_count. The system SHOULD support update_frequency
          metadata for consumers to understand data freshness.
          Actors: ACT-S001, ACT-S002.

CAP-S008: The system MUST support creation, versioning, and comparison
          of SpatialDatasets (TERM-S007). The system MUST support
          dataset version comparison: given two versions, identify
          features added, modified, and removed. The system MUST enforce
          immutability of published dataset versions. The system MUST
          support ISO 19115 metadata and ISO 19157 quality elements.
          Actors: ACT-S002, ACT-S007.

CAP-S009: The system MUST support creation and querying of Rasters
          (TERM-S008). The system MUST support multi-band rasters. The
          system MUST compute per-band statistics. The system SHOULD
          support tiled raster access for efficient partial retrieval.
          The system MUST distinguish raster data (continuous fields)
          from vector data (discrete features) in query interfaces.
          Actors: ACT-S001, ACT-S002.
```

### Spatial Relationships & Constraints

```
CAP-S010: The system MUST support computation and querying of
          SpatialRelationships (TERM-S009). The system MUST support all
          DE-9IM topological predicates: contains, within, intersects,
          overlaps, touches, crosses, disjoint, equals, covers,
          covered_by. The system MUST support metric relationships:
          within_distance (find all features within N meters) and
          nearest_k (find K nearest features). Metric distance MUST
          support geodesic, euclidean, and network metrics. The system
          MUST propagate accuracy to relationship confidence.
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S005.

CAP-S011: The system MUST support creation and evaluation of
          SpatialConstraints (TERM-S010). The system MUST support
          constraint hardness levels (hard, soft, preference). When
          evaluating a set of constraints, the system MUST report which
          constraints are satisfied and which are violated. When no
          feasible solution exists, soft and preference constraints MUST
          be relaxable in relaxation_priority order. Hard constraint
          infeasibility MUST be reported to human authority.
          Actors: ACT-S001, ACT-S002, ACT-S003, ACT-S004.

CAP-S012: The system MUST support creation and querying of SpatialIndexes
          (TERM-S011). The system MUST support at least one hierarchical
          spatial indexing scheme (H3, S2, or geohash). The system MUST
          support cell_id lookup for any Location at any supported
          resolution. The system MUST support spatial queries via index:
          "all features in cell X," "all cells intersecting polygon Y,"
          "neighboring cells of cell Z."
          Actors: ACT-S001, ACT-S002, ACT-S003, ACT-S004.
```

### Routing & Network Analysis

```
CAP-S013: The system MUST support creation and management of
          SpatialNetworks (TERM-S012). The system MUST support multiple
          network types (road, transit, pedestrian, cycling, etc.). The
          system MUST enforce connectivity rules (turn restrictions,
          access restrictions). The system MUST support temporal_validity
          for networks that change over time.
          Actors: ACT-S001, ACT-S002.

CAP-S014: The system MUST support creation and management of
          NetworkSegments (TERM-S013) with travel characteristics. The
          system MUST support access_restrictions by vehicle type and
          time of day. The system MUST support segment condition
          tracking (open, restricted, closed, planned,
          under_construction). When a segment condition changes, the
          system MUST evaluate affected Routes for invalidation.
          Actors: ACT-S001, ACT-S002, ACT-S003, ACT-S004.

CAP-S015: The system MUST support Route computation (TERM-S014) from
          origin to destination via SpatialNetwork. The system MUST
          support multiple optimization criteria (shortest, fastest,
          cheapest, avoid_tolls, avoid_highways, truck_safe). The system
          MUST support waypoints. The system SHOULD return alternative
          routes. The system MUST support vehicle_profile constraints
          (height, width, weight, hazmat). Route computation MUST produce
          total_distance_m and estimated_duration_s. The system MUST
          assign validity_window to computed Routes.
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S005, ACT-S008.

CAP-S016: The system MUST support ServiceArea computation (TERM-S015)
          as isochrone (time-based), isodistance (distance-based), or
          isocost (cost-based) reachability from an origin Location. The
          system MUST support contour_intervals for graduated service
          areas (5/10/15 minute rings). The system MUST return the
          resulting area as a SpatialGeometry polygon. ServiceArea
          computation MUST respect network constraints and vehicle
          profile.
          Actors: ACT-S001, ACT-S003, ACT-S004.

CAP-S017: The system MUST support Route invalidation when SpatialChange
          (TERM-S030) affects any NetworkSegment in an active Route. The
          system MUST emit substrate.spatial.route.invalidated events for
          all affected Routes. The system SHOULD support automatic route
          recomputation for active Routes when invalidated.
          Actors: ACT-S003, ACT-S004 (automated), ACT-S002 (manual).
```

### Zone, Territory & Boundary Management

```
CAP-S018: The system MUST support creation, modification, and lifecycle
          management of Zones (TERM-S016). Zones follow SM-S003
          (proposed → active → suspended | dissolved). The system MUST
          support hierarchical zone nesting (city within county within
          state). The system MUST support zone_type classification with
          appropriate governance integration per type.
          Actors: ACT-S001, ACT-S002, ACT-S004.

CAP-S019: The system MUST support Territory (TERM-S017) creation,
          assignment, and rebalancing. Territories follow SM-S005
          (proposed → active → under_review → active | dissolved). The
          system MUST support performance_metrics tracking. The system
          MUST support rebalancing_trigger evaluation and constraint-
          based rebalancing (minimize disruption, maintain contiguity).
          Territory rebalancing SHOULD be delegated to COMPUTE Pipeline
          for optimization.
          Actors: ACT-S002, ACT-S004.

CAP-S020: The system MUST support Boundary (TERM-S018) creation and
          management with crossing rules. The system MUST support the
          disputed flag for sovereignty disputes (UNK-S005). The system
          MUST support multiple boundary claims for the same geographic
          line as separate entities. The system MUST support
          transition_requirements for borders requiring inspection,
          customs, or toll.
          Actors: ACT-S002.

CAP-S021: The system MUST support point-in-zone queries: given a
          Location, determine which Zone(s) contain it. The system MUST
          support multi-zone membership (a Location may be in a city
          zone AND a flood hazard zone AND a delivery zone
          simultaneously). The system MUST use SpatialIndex for
          efficient zone lookup.
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S005, ACT-S008.
```

### Place, Geocoding & Movement

```
CAP-S022: The system MUST support creation and querying of Places
          (TERM-S019) with multilingual naming and hierarchical
          geographic context. The system MUST support place_type
          classification. The system MUST support place hierarchy
          navigation (city → state → country → continent). The system
          MUST support Place search by name with disambiguation via
          hierarchy.
          Actors: ACT-S001, ACT-S002, ACT-S005, ACT-S008.

CAP-S023: The system MUST support forward geocoding (text → Location
          candidates) and reverse geocoding (Location → Address) with
          full GeocodingResult (TERM-S020) audit trail. Every geocoding
          operation MUST produce ranked candidates with confidence
          scores. The system MUST track selection_method (highest_
          confidence, user_selected, ai_agent_selected). The system
          MUST support batch geocoding. GeocodingResult follows SM-S004
          (pending → resolved | ambiguous | failed).
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S005, ACT-S006.

CAP-S024: The system MUST support Trajectory (TERM-S021) recording,
          querying, and analysis. The system MUST compute total_distance,
          dwell_points, and transport_mode. The system MUST support
          trajectory simplification (Douglas-Peucker, Visvalingam) for
          storage optimization. The system MUST apply SpatialPolicy
          privacy rules to trajectory data (spatial cloaking, temporal
          cloaking, precision degradation). The system MUST support
          temporal queries ("trajectory between time A and time B").
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S006 (GPS feeds).
```

### Coverage, Density & Proximity

```
CAP-S025: The system MUST support Coverage (TERM-S022) computation:
          given a set of resource locations and a target area, compute
          coverage_percentage, gap_areas, and overlap_areas. The system
          MUST support coverage_standard_ref for regulatory compliance
          checking. The system MUST support Coverage invalidation when
          SpatialChange affects underlying resources.
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S007.

CAP-S026: The system MUST support Density (TERM-S023) computation using
          at least one method (kernel density estimation, grid count, or
          hexbin aggregation). The system MUST return results as Raster
          or vector output with units and statistics. The system SHOULD
          support configurable resolution and kernel bandwidth.
          Actors: ACT-S001, ACT-S003, ACT-S004.

CAP-S027: The system MUST support ProximityRule (TERM-S024) creation,
          evaluation, and trigger management. The system MUST support
          continuous monitoring of entity positions against geofence
          geometries. The system MUST support enter/exit/both trigger
          directions. The system MUST support cooldown periods to prevent
          repeated triggers. The system MUST emit substrate.spatial.
          proximity.triggered events when rules fire. The system MUST
          apply active_window temporal constraints when configured.
          Actors: ACT-S001, ACT-S002, ACT-S003, ACT-S004.
```

### Indoor Spatial

```
CAP-S028: The system MUST support Floor (TERM-S025) creation and
          management within buildings. The system MUST support level
          numbering (including negative for underground levels). The
          system MUST support vertical_connections between floors (stairs,
          elevators, escalators, ramps) for indoor routing.
          Actors: ACT-S001, ACT-S002.

CAP-S029: The system MUST support IndoorSpace (TERM-S026) creation and
          management within Floors. The system MUST support
          connected_spaces adjacency for indoor routing graph
          construction. The system MUST support capacity tracking. The
          system SHOULD support accessibility_features for ADA/
          accessibility-compliant wayfinding. The system MUST support
          cross-substrate reference to TEMPORAL SchedulableResource for
          bookable rooms.
          Actors: ACT-S001, ACT-S002.

CAP-S030: The system SHOULD support indoor-outdoor seamless routing:
          given an outdoor origin and an indoor destination (or vice
          versa), compute a route that bridges the outdoor SpatialNetwork,
          building entry, vertical connections (Floor), and indoor
          connected_spaces graph. The system MUST handle the indoor/
          outdoor discontinuity (Property S4) by joining outdoor network
          routing with indoor graph traversal at building entry points.
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S005.
```

### Spatial Authority, Policy & Change Management

```
CAP-S031: The system MUST enforce SpatialEnvelope (TERM-S027) for all
          AI agent spatial operations. The system MUST check
          max_geographic_scope, dataset access, and operation-specific
          authority (geocoding, routing, zone modification, feature
          creation, territory assignment) before executing each AI agent
          request. Envelope violations MUST be blocked and logged.
          Actors: ACT-S003, ACT-S004 (subject to), ACT-S002 (configures).

CAP-S032: The system MUST enforce SpatialPolicy (TERM-S028) rules per
          actor and context. The system MUST apply privacy precision
          degradation at query boundaries — full-precision data stored
          internally, degraded precision exposed per policy. The system
          MUST enforce retention policies (delete/archive per configured
          schedule). The system MUST enforce quality policies (reject
          spatial data below minimum accuracy threshold).
          Actors: all (subject to), ACT-S002 (configures).

CAP-S033: The system MUST maintain SpatialAccuracy (TERM-S029) metadata
          for all spatial measurements. Accuracy MUST propagate through
          spatial operations: the output accuracy of any operation is at
          most as good as its least-accurate input. The system MUST
          support accuracy degradation tracking over time
          (degradation_rate). The system SHOULD warn when spatial data
          exceeds staleness_threshold without re-verification.
          Actors: all (benefit from), ACT-S002 (configures thresholds),
          ACT-S007 (audits).

CAP-S034: The system MUST support SpatialChange (TERM-S030) detection,
          recording, and cascade analysis. When a spatial change is
          detected (road closure, building demolition, zone boundary
          modification), the system MUST identify all affected downstream
          computations (Routes, ServiceAreas, Coverages, Territories).
          The system MUST emit substrate.spatial.change.detected events.
          The system MUST support both permanent and temporary changes
          with end_datetime for temporary changes. The system SHOULD
          support automatic recomputation triggers for critical spatial
          computations (active Routes, coverage analyses under regulatory
          standard).
          Actors: ACT-S001, ACT-S002, ACT-S003, ACT-S004, ACT-S006.
```

---

## 5. DOMAIN OBJECTS & STATE

> Entity identifiers follow the pattern ENT-S###. Each entity maps to
> one TERM-S### primitive defined in Section 3. State machines are
> labeled SM-S###. Fields not already fully specified in Section 3 are
> elaborated here; all fields from Section 3 definitions are inherited.

### 5.1 Entity List

```
ENT-S001: CoordinateReferenceSystem entity. TERM-S001.
          Key: crs_id (UUID). Natural key: epsg_code (when non-null).
          Lifecycle: created → active | deprecated.
          Indexes: epsg_code (unique when non-null), geodetic_datum,
          authority.

ENT-S002: Location entity. TERM-S002.
          Key: location_id (UUID).
          Lifecycle: created → current | historical | invalidated.
          Indexes: (latitude, longitude) via SpatialIndex, timestamp,
          source, floor_ref. Spatial index: H3 cell at resolution 9
          (default) for proximity queries.

ENT-S003: Address entity. TERM-S003.
          Key: address_id (UUID). Natural key: (formatted_address,
          country_code) — not unique (same address text may map to
          multiple geocoded locations).
          Lifecycle: created → resolved | ambiguous | unresolved.
          Indexes: country_code, postal_code, city, resolution_status.
          Full-text index on formatted_address for autocomplete.

ENT-S004: SpatialGeometry entity. TERM-S004.
          Key: geometry_id (UUID).
          Lifecycle: created (immutable after validation — geometries are
          versioned, not mutated; a modified geometry is a new entity).
          Indexes: bounding_box (R-tree or equivalent), geometry_type.
          Spatial index on bounding_box for intersection queries.

ENT-S005: SpatialFeature entity. TERM-S005.
          Key: feature_id (UUID).
          Lifecycle: SM-S001 (draft → active → archived | superseded).
          Indexes: feature_type, layer_ref, geometry bounding_box (via
          geometry_ref), temporal_validity, status, version.

ENT-S006: Layer entity. TERM-S006.
          Key: layer_id (UUID). Natural key: (name, dataset_ref).
          Lifecycle: created → active → archived.
          Indexes: dataset_ref, name, feature_count, update_frequency.

ENT-S007: SpatialDataset entity. TERM-S007.
          Key: dataset_id (UUID). Version key: (dataset_id, version).
          Lifecycle: draft → published → superseded | archived.
          Constraint: published datasets are immutable.
          Indexes: name, version, status, spatial_extent.

ENT-S008: Raster entity. TERM-S008.
          Key: raster_id (UUID).
          Lifecycle: created → active → archived.
          Indexes: bounds (spatial), resolution, band count,
          temporal_validity.

ENT-S009: SpatialRelationship entity. TERM-S009.
          Key: relationship_id (UUID).
          Lifecycle: computed → valid | expired (when underlying features
          change).
          Indexes: (source_ref, target_ref), relationship_type,
          computed_distance.

ENT-S010: SpatialConstraint entity. TERM-S010.
          Key: constraint_id (UUID).
          Lifecycle: created → active → suspended | retired.
          Indexes: constraint_type, hardness, governing_ref,
          temporal_validity.

ENT-S011: SpatialIndex entity. TERM-S011.
          Key: index_id (UUID).
          Lifecycle: created → active → rebuilding → active.
          Indexes: index_type, resolution, coverage_area.

ENT-S012: SpatialNetwork entity. TERM-S012.
          Key: network_id (UUID).
          Lifecycle: created → active → archived.
          Indexes: network_type, coverage_area (spatial),
          temporal_validity.

ENT-S013: NetworkSegment entity. TERM-S013.
          Key: segment_id (UUID).
          Lifecycle: created → active → closed | archived.
          Indexes: network_ref, (from_node, to_node), condition,
          road_class, geometry bounding_box.

ENT-S014: Route entity. TERM-S014.
          Key: route_id (UUID).
          Lifecycle: SM-S002 (computed → active → completed |
          invalidated).
          Indexes: origin (spatial), destination (spatial), status,
          computed_at, validity_window.

ENT-S015: ServiceArea entity. TERM-S015.
          Key: service_area_id (UUID).
          Lifecycle: computed → valid → expired (when underlying network
          changes).
          Indexes: origin (spatial), constraint_type, constraint_value,
          resulting_geometry (spatial).

ENT-S016: Zone entity. TERM-S016.
          Key: zone_id (UUID). Natural key: (name, zone_type,
          hierarchy_parent_ref).
          Lifecycle: SM-S003 (proposed → active → suspended | dissolved).
          Indexes: zone_type, geometry (spatial), hierarchy_parent_ref,
          hierarchy_level, status.

ENT-S017: Territory entity. TERM-S017.
          Key: territory_id (UUID).
          Lifecycle: SM-S005 (proposed → active → under_review → active
          | dissolved).
          Indexes: assignee_ref, geometry (spatial), zone_ref, status.

ENT-S018: Boundary entity. TERM-S018.
          Key: boundary_id (UUID).
          Lifecycle: created → active → superseded | dissolved.
          Indexes: left_zone_ref, right_zone_ref, disputed, geometry
          (spatial).

ENT-S019: Place entity. TERM-S019.
          Key: place_id (UUID).
          Lifecycle: created → active → archived.
          Indexes: name (full-text, multilingual), place_type, geometry
          (spatial), hierarchy path, population.

ENT-S020: GeocodingResult entity. TERM-S020.
          Key: geocoding_result_id (UUID).
          Lifecycle: SM-S004 (pending → resolved | ambiguous | failed).
          Indexes: input text (full-text), result_type, ambiguity_flag,
          computed_at.

ENT-S021: Trajectory entity. TERM-S021.
          Key: trajectory_id (UUID).
          Lifecycle: active → completed → archived.
          Indexes: entity_ref, start_time, end_time, transport_mode,
          positions (spatial-temporal).

ENT-S022: Coverage entity. TERM-S022.
          Key: coverage_id (UUID).
          Lifecycle: computed → valid → stale (when underlying data
          changes).
          Indexes: resource_type, service_type, target_area (spatial),
          coverage_percentage, computed_at.

ENT-S023: Density entity. TERM-S023.
          Key: density_id (UUID).
          Lifecycle: computed → valid → stale.
          Indexes: feature_type, area_ref (spatial), computation_method,
          computed_at.

ENT-S024: ProximityRule entity. TERM-S024.
          Key: proximity_rule_id (UUID).
          Lifecycle: created → active → paused → active | expired.
          Indexes: source_entity_ref, target_geometry (spatial), status,
          last_triggered_at.

ENT-S025: Floor entity. TERM-S025.
          Key: floor_id (UUID). Natural key: (building_ref, level_number).
          Lifecycle: created → active → archived.
          Indexes: building_ref, level_number, geometry (spatial).

ENT-S026: IndoorSpace entity. TERM-S026.
          Key: indoor_space_id (UUID).
          Lifecycle: created → active → archived.
          Indexes: floor_ref, space_type, name, geometry (spatial),
          capacity.

ENT-S027: SpatialEnvelope entity. TERM-S027.
          Key: envelope_id (UUID).
          Lifecycle: created → active → suspended → active | revoked.
          Indexes: agent_ref, max_geographic_scope (spatial).

ENT-S028: SpatialPolicy entity. TERM-S028.
          Key: policy_id (UUID).
          Lifecycle: created → active → suspended → active | retired.
          Indexes: policy_type, scope, enforcement, temporal_validity.

ENT-S029: SpatialAccuracy entity. TERM-S029.
          Key: accuracy_id (UUID).
          Lifecycle: created (immutable — accuracy metadata is a
          measurement record, not mutable state).
          Indexes: accuracy_method, horizontal_accuracy_m,
          last_verified_at.

ENT-S030: SpatialChange entity. TERM-S030.
          Key: change_id (UUID).
          Lifecycle: detected → analyzing → cascaded → resolved.
          Indexes: change_type, affected_area (spatial),
          effective_datetime, severity, duration_type.
```

### 5.2 State Machines

```
SM-S001: SpatialFeature Lifecycle
         States: draft, active, archived, superseded
         Transitions:
           draft → active:       Feature validated (geometry valid, accuracy
                                 metadata present, layer schema conformant).
                                 Actors: ACT-S001, ACT-S002.
           active → archived:    Feature no longer represents current
                                 reality (building demolished, road
                                 decommissioned). Sets temporal_validity.
                                 valid_to. Actors: ACT-S001, ACT-S002.
           active → superseded:  New version of feature created with
                                 updated geometry or properties. Old
                                 version marked superseded with pointer
                                 to new version. Actors: ACT-S001,
                                 ACT-S002, ACT-S003, ACT-S004.
         Invariant: Only active features participate in spatial queries
                    (unless historical query mode is explicitly requested).
         Invariant: Superseded features retain full data for historical
                    reconstruction.

SM-S002: Route Lifecycle
         States: computed, active, completed, invalidated
         Transitions:
           computed → active:      Route accepted for use (by human or
                                   system). Actors: ACT-S001, ACT-S003,
                                   ACT-S004, ACT-S005.
           active → completed:     Journey along route finished
                                   (Trajectory records actual path).
                                   Actors: system (on trajectory
                                   completion).
           active → invalidated:   SpatialChange (TERM-S030) affects one
                                   or more segments. System emits
                                   substrate.spatial.route.invalidated.
                                   Actors: system (automatic on
                                   SpatialChange).
           computed → invalidated: Route never activated but underlying
                                   data changed. Actors: system.
         Invariant: Invalidated routes retain data for audit/comparison
                    (what was the planned route vs what happened).

SM-S003: Zone Lifecycle
         States: proposed, active, suspended, dissolved
         Transitions:
           proposed → active:     Zone approved by governing authority.
                                  Actors: ACT-S002 (with ACT-S004
                                  recommendation).
           active → suspended:    Zone temporarily inactive (seasonal
                                  zone, emergency suspension).
                                  Actors: ACT-S002.
           suspended → active:    Zone reactivated.
                                  Actors: ACT-S002.
           active → dissolved:    Zone permanently ended (redistricting,
                                  annexation, merger). Sets temporal_
                                  validity.valid_to.
                                  Actors: ACT-S002.
           proposed → dissolved:  Zone proposal rejected.
                                  Actors: ACT-S002.
         Invariant: Dissolved zones retain boundary data for historical
                    queries.

SM-S004: GeocodingResult Lifecycle
         States: pending, resolved, ambiguous, failed
         Transitions:
           pending → resolved:    A candidate selected (highest confidence,
                                  user selection, AI agent selection, or
                                  policy default). Actors: ACT-S001,
                                  ACT-S003, ACT-S004, ACT-S005.
           pending → ambiguous:   Multiple candidates with confidence > 0.5
                                  and no selection made. Requires human
                                  or AI disambiguation. Actors: system.
           pending → failed:      No candidates match input. Actors: system.
           ambiguous → resolved:  Candidate selected from ambiguous set.
                                  Actors: ACT-S001, ACT-S003, ACT-S005.
         Invariant: All candidates and the selection decision are retained
                    in the audit trail regardless of final state.

SM-S005: Territory Lifecycle
         States: proposed, active, under_review, dissolved
         Transitions:
           proposed → active:      Territory approved and assignee
                                   confirmed. Actors: ACT-S002, ACT-S004.
           active → under_review:  Rebalancing trigger fires (threshold
                                   breach, periodic evaluation, demand
                                   shift). Actors: system (on trigger),
                                   ACT-S002 (manual).
           under_review → active:  Rebalancing completed or manual
                                   confirmation. Updated geometry,
                                   assignee, or metrics.
                                   Actors: ACT-S002, ACT-S004.
           active → dissolved:     Territory no longer needed (assignee
                                   departed, organizational restructure).
                                   Actors: ACT-S002.
           under_review → dissolved: Territory dissolved during review.
                                   Actors: ACT-S002.
         Invariant: Performance metrics history retained for all states
                    (enables fairness auditing per ACT-S007).
```

---

## 6. INTERFACES

> Interface identifiers follow the pattern IFC-S###. Each interface
> defines a contract between SUBSTRATE-SPATIAL and external consumers
> (human actors, AI agents, peer substrates, external systems).

```
IFC-S001: Spatial Feature Interface
          Operations:
            — createFeature(feature_type, geometry, properties, layer_ref,
              accuracy_ref) → SpatialFeature
            — updateFeature(feature_id, geometry?, properties?) →
              SpatialFeature (new version, old version superseded)
            — archiveFeature(feature_id, reason) → SpatialFeature
            — getFeature(feature_id, version?) → SpatialFeature
            — queryFeatures(bbox?, geometry_filter?, feature_type?,
              layer_ref?, temporal_range?, properties_filter?) →
              SpatialFeature[]
          Actors: ACT-S001, ACT-S002, ACT-S003, ACT-S004, ACT-S005.
          Auth: SpatialEnvelope (for AI agents), SpatialPolicy access
          rules (for all actors).
          Events: substrate.spatial.feature.created,
          substrate.spatial.feature.updated,
          substrate.spatial.feature.archived.

IFC-S002: Geocoding Interface
          Operations:
            — geocodeForward(address_text, country_hint?, bounds_hint?)
              → GeocodingResult (with candidates[])
            — geocodeReverse(latitude, longitude, radius_m?) →
              GeocodingResult (with nearest address candidates)
            — geocodeBatch(addresses[]) → GeocodingResult[]
            — selectCandidate(geocoding_result_id, candidate_idx,
              selection_method) → GeocodingResult (resolved)
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S005, ACT-S006,
          ACT-S008.
          Auth: SpatialPolicy precision rules determine result precision
          per actor. External actors (ACT-S008) receive degraded
          precision per TRUST-S001.
          Events: substrate.spatial.geocoding.completed,
          substrate.spatial.geocoding.ambiguous.

IFC-S003: Routing Interface
          Operations:
            — computeRoute(origin, destination, waypoints?, network_type?,
              optimization_criterion?, vehicle_profile?, avoid_features?
              []) → Route (with alternatives[])
            — computeRouteMatrix(origins[], destinations[],
              optimization_criterion?) → {distance_m[][], duration_s[][]}
            — computeServiceArea(origin, constraint_type, constraint_
              value, network_type?, vehicle_profile?, contour_intervals?
              []) → ServiceArea
            — invalidateRoute(route_id, reason, spatial_change_ref) →
              Route (invalidated)
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S005, ACT-S008.
          Auth: SpatialEnvelope routing_authority for AI agents.
          SpatialPolicy for external actor rate limiting.
          Events: substrate.spatial.route.computed,
          substrate.spatial.route.invalidated,
          substrate.spatial.service_area.computed.

IFC-S004: Zone & Territory Interface
          Operations:
            — createZone(name, zone_type, geometry, rules?, governing_
              authority_ref?, parent_zone_ref?) → Zone
            — modifyZoneBoundary(zone_id, new_geometry, reason) → Zone
            — queryZonesContaining(location) → Zone[]
            — createTerritory(name, assignee_ref, geometry,
              assignment_criteria, performance_metrics?) → Territory
            — rebalanceTerritories(territory_ids[], constraints) →
              Territory[] (rebalanced)
            — createBoundary(geometry, left_zone_ref?, right_zone_ref?,
              crossing_rules) → Boundary
          Actors: ACT-S002 (create/modify), ACT-S004 (rebalance),
          ACT-S001 (query), ACT-S005 (query).
          Auth: SpatialEnvelope zone_modification_authority and
          territory_assignment_authority for AI agents.
          Events: substrate.spatial.zone.created,
          substrate.spatial.zone.boundary_modified,
          substrate.spatial.territory.assigned,
          substrate.spatial.territory.rebalanced.

IFC-S005: Spatial Relationship Interface
          Operations:
            — computeRelationship(source_geometry, target_geometry,
              relationship_type) → SpatialRelationship
            — queryWithinDistance(origin, distance_m, distance_metric?,
              feature_type?) → SpatialFeature[]
            — queryNearestK(origin, k, feature_type?) →
              {feature: SpatialFeature, distance_m: float64}[]
            — evaluateConstraints(constraints[], features[]) →
              {constraint_id, satisfied: boolean, violation_detail?}[]
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S005.
          Auth: SpatialPolicy access rules.
          Events: substrate.spatial.constraint.violated (when evaluation
          finds hard constraint violation).

IFC-S006: Trajectory Interface
          Operations:
            — startTrajectory(entity_ref, transport_mode) → Trajectory
            — appendPosition(trajectory_id, location, timestamp, speed?,
              heading?) → Trajectory (updated)
            — completeTrajectory(trajectory_id) → Trajectory (completed)
            — queryTrajectory(trajectory_id, time_range?) → Trajectory
            — queryTrajectoriesByEntity(entity_ref, time_range?) →
              Trajectory[]
            — simplifyTrajectory(trajectory_id, algorithm, tolerance) →
              Trajectory (simplified)
          Actors: ACT-S001, ACT-S003, ACT-S006 (position feeds).
          Auth: SpatialPolicy privacy rules for trajectory access.
          Trajectory data precision degraded per actor trust level.
          Events: substrate.spatial.trajectory.started,
          substrate.spatial.trajectory.completed.

IFC-S007: Coverage & Density Interface
          Operations:
            — computeCoverage(resource_locations[], target_area,
              service_type, coverage_standard_ref?) → Coverage
            — computeDensity(features, area, computation_method,
              resolution) → Density
            — queryCoverageGaps(coverage_id) → SpatialGeometry[]
          Actors: ACT-S001, ACT-S003, ACT-S004, ACT-S007.
          Auth: SpatialPolicy access rules.
          Events: substrate.spatial.coverage.computed,
          substrate.spatial.coverage.gap_detected.

IFC-S008: Indoor Spatial Interface
          Operations:
            — createFloor(building_ref, level_number, geometry, name) →
              Floor
            — createIndoorSpace(floor_ref, space_type, geometry, name,
              capacity?, connected_spaces?) → IndoorSpace
            — computeIndoorRoute(origin_space, destination_space) →
              {path: IndoorSpace[], total_distance_m, estimated_
              duration_s}
            — querySpacesOnFloor(floor_id, space_type?) → IndoorSpace[]
          Actors: ACT-S001, ACT-S002.
          Auth: SpatialPolicy access rules. Indoor data may have
          different access policies than outdoor data.
          Events: substrate.spatial.indoor.space_created.

IFC-S009: Spatial Change Interface
          Operations:
            — reportChange(change_type, affected_area, description,
              effective_datetime, duration_type, severity) →
              SpatialChange (with cascade_analysis)
            — querySpatialChanges(area?, time_range?, change_type?,
              severity?) → SpatialChange[]
            — acknowledgeChange(change_id, response_actions[]) →
              SpatialChange (acknowledged)
          Actors: ACT-S001, ACT-S002, ACT-S003, ACT-S006.
          Auth: Feature creation authority for reporting changes.
          Events: substrate.spatial.change.detected,
          substrate.spatial.change.cascade_computed,
          substrate.spatial.change.acknowledged.

IFC-S010: Spatial Policy & Envelope Interface
          Operations:
            — createPolicy(name, policy_type, scope, rules, enforcement)
              → SpatialPolicy
            — createEnvelope(agent_ref, max_geographic_scope,
              authorities) → SpatialEnvelope
            — validateEnvelope(agent_ref, operation, parameters) →
              {permitted: boolean, violation_detail?}
            — degradePrecision(location, target_precision_level) →
              Location (degraded)
          Actors: ACT-S002 (create/modify), system (validate).
          Auth: Steward authority for policy/envelope management.
          Events: substrate.spatial.envelope.violation,
          substrate.spatial.policy.created.
```

---

## 7. DATA FLOWS

> Data flow identifiers follow the pattern FLOW-S###. Each flow
> describes data movement between actors, interfaces, and entities.
> Cross-substrate flows reference integration contracts (INT-S###).

```
FLOW-S001: Feature Creation & Validation
           Trigger: ACT-S001 or ACT-S006 submits spatial feature data.
           1. Validate SpatialGeometry (OGC Simple Features compliance).
           2. Validate accuracy metadata (SpatialAccuracy present,
              meets SpatialPolicy quality threshold).
           3. Validate against Layer feature_schema (if layer_ref
              provided).
           4. Assign SpatialIndex cell_ids at configured resolutions.
           5. Persist feature (event: feature.created).
           6. Evaluate SpatialConstraints applicable to the feature's
              location and type.
           7. If constraint violated: emit substrate.spatial.constraint
              .violated.
           Output: SpatialFeature (ENT-S005) in draft or active state.

FLOW-S002: Geocoding Pipeline
           Trigger: ACT-S001/S003/S005/S008 submits address text or
           coordinates.
           1. Parse input (libpostal-style statistical parser for
              address text; coordinate validation for reverse).
           2. Query geocoding databases (national address DB, OSM,
              commercial providers — implementation-dependent).
           3. Score candidates (exact > interpolated > centroid >
              approximate).
           4. Construct GeocodingResult with ranked candidates.
           5. Apply SpatialPolicy precision degradation per actor
              trust level.
           6. If ambiguity_flag: await candidate selection or apply
              policy default.
           7. Persist GeocodingResult (event: geocoding.completed
              or geocoding.ambiguous).
           Output: GeocodingResult (ENT-S020).

FLOW-S003: Route Computation
           Trigger: ACT-S001/S003/S005 requests route via IFC-S003.
           1. Resolve origin/destination Locations (geocode if
              address provided).
           2. Select SpatialNetwork by network_type.
           3. Apply vehicle_profile constraints (filter segments by
              access_restrictions).
           4. Construct RoutingProblem (INT-S002 schema).
           5. Delegate to COMPUTE Pipeline for solver execution
              (Dijkstra, A*, Contraction Hierarchies — solver is
              implementation-dependent).
           6. Receive RoutingSolution with segments, distance, duration.
           7. Assign validity_window based on network volatility.
           8. Compute accuracy_ref from underlying segment accuracy.
           9. Persist Route (event: route.computed).
           Output: Route (ENT-S014) with alternatives[].

FLOW-S004: Spatial Change Cascade (cross-substrate)
           Trigger: SpatialChange detected (road closure, building
           demolition, zone boundary modification).
           1. Record SpatialChange (ENT-S030) with affected_area.
           2. Query SpatialIndex for features intersecting affected_area.
           3. Identify affected Routes (segments within affected_area).
           4. Identify affected ServiceAreas (origin reachability changed).
           5. Identify affected Coverages (resource availability changed).
           6. Identify affected Territories (boundary/performance impact).
           7. Compute cascade_analysis summary.
           8. Emit substrate.spatial.change.detected with cascade data.
           9. Invalidate affected Routes (SM-S002: active → invalidated).
           10. Cross-substrate: TEMPORAL receives event → creates
               Disruption for scheduled activities at invalidated
               locations. BUSINESS receives event → replans affected
               deliveries.
           Output: SpatialChange with cascade_analysis; invalidated
           downstream entities; cross-substrate events.

FLOW-S005: Travel Duration Resolution (cross-substrate: TEMPORAL)
           Trigger: TEMPORAL emits substrate.temporal.travel_duration
           .requested with location_from, location_to, time_of_departure.
           1. SPATIAL receives request via INT-S001.
           2. Resolve Locations (geocode if addresses provided).
           3. Compute Route (FLOW-S003) with optimization_criterion:
              fastest, traffic_model appropriate for time_of_departure.
           4. Return RoutingSolution with total_distance_m and
              estimated_duration_s.
           5. TEMPORAL consumes duration for TransitionTime scheduling.
           Output: RoutingSolution consumed by TEMPORAL TransitionTime.

FLOW-S006: Site Planning Composition (cross-substrate: DESIGN)
           Trigger: DESIGN site planning requires geographic context.
           1. DESIGN provides building Geometry + Requirements (setbacks,
              utilities, access).
           2. SPATIAL queries SpatialFeatures in site vicinity (neighboring
              structures, roads, water bodies, utilities, terrain).
           3. SPATIAL evaluates SpatialConstraints (setback requirements,
              flood zone exclusions, utility corridor buffers).
           4. SPATIAL returns site context: features, constraints, and
              compliance assessment.
           5. DESIGN uses context for site layout optimization.
           Output: Site context data consumed by DESIGN for artifact
           placement.

FLOW-S007: Jurisdiction Geography Sync (cross-substrate: GOVERNANCE)
           Trigger: Zone boundary change (redistricting, annexation) or
           new Jurisdiction creation.
           1. SPATIAL updates Zone (zone_type: administrative) geometry.
           2. SPATIAL emits substrate.spatial.zone.boundary_modified.
           3. GOVERNANCE receives event → updates Jurisdiction
              geographic_extent_ref.
           4. GOVERNANCE re-evaluates norm applicability for entities
              affected by boundary change.
           Output: Synchronized Zone boundaries between SPATIAL and
           GOVERNANCE Jurisdiction.

FLOW-S008: Fleet Tracking Pipeline (cross-substrate: PHYSICAL, TEMPORAL)
           Trigger: PHYSICAL emits substrate.physical.asset.relocated
           with GPS position.
           1. SPATIAL receives Location data from PHYSICAL sensor feed.
           2. SPATIAL updates or creates Location (ENT-S002) for asset.
           3. SPATIAL appends position to active Trajectory (ENT-S021).
           4. SPATIAL evaluates ProximityRules against new position.
           5. If ProximityRule triggered: emit substrate.spatial.proximity
              .triggered.
           6. If asset deviates from planned Route: evaluate Route
              adherence and optionally trigger rerouting.
           7. TEMPORAL consumes position data for schedule adherence
              tracking (is the delivery on time?).
           Output: Updated Location, Trajectory, ProximityRule
           evaluations; cross-substrate events to TEMPORAL/BUSINESS.
```

---

## 8. INTEGRATION CONTRACTS

> Integration contract identifiers follow the pattern INT-S###. Each
> contract defines the protocol between SUBSTRATE-SPATIAL and a peer
> substrate, including event schemas, delegation tables, and data
> ownership boundaries.

```
INT-S001: SPATIAL ↔ TEMPORAL — Travel Duration Resolution
          Protocol:
            1. TEMPORAL emits: substrate.temporal.travel_duration.requested
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
            2. SPATIAL computes Route via FLOW-S003.
            3. SPATIAL emits: substrate.spatial.route.computed
               Payload (RoutingSolution schema):
                 {route_id, total_distance_m, estimated_duration_s,
                  segments: [{segment_id, length_m, travel_time_s}],
                  alternatives: [{route_id, distance_m, duration_s}],
                  accuracy_ref, computation_time_ms}
            4. TEMPORAL consumes duration for TransitionTime (TERM-T029).
          Ownership: SPATIAL owns Route computation. TEMPORAL owns
          scheduling decision based on duration.
          SLA: Route computation ≤1s for single origin-destination
          (RUNTIME-S003 Tier 2).
          Mirror: INT-T008 in SUBSTRATE-TEMPORAL.

INT-S002: SPATIAL ↔ COMPUTE — Spatial Computation Delegation
          Protocol:
            1. SPATIAL constructs SpatialProblem:
               Types: routing_optimization (multi-stop VRP), coverage_
               optimization (facility placement), territory_rebalancing,
               large_scale_spatial_join, network_analysis.
               Payload: {problem_type, input_data (features, network,
                 constraints), objective (minimize_distance, maximize_
                 coverage, balance_workload), constraints[], solver_
                 hints (algorithm preference, time_limit_s, gap_tolerance)}
            2. SPATIAL submits to COMPUTE Pipeline.
            3. COMPUTE executes solver (implementation-dependent: OR-Tools,
               OptaPlanner, PostGIS, custom).
            4. COMPUTE returns SpatialSolution:
               {solution_type, result_data (routes[], placements[],
                 territories[]), objective_value, computation_time_ms,
                 optimality_gap, solver_used}
            5. SPATIAL consumes solution and creates/updates entities.
          Ownership: SPATIAL owns problem definition and solution
          interpretation. COMPUTE owns solver execution.
          SLA: per problem type (RUNTIME-S003 Tier 3-4).

INT-S003: SPATIAL ↔ BUSINESS — Location Services
          Protocol:
            — BUSINESS references SPATIAL Address for customer/vendor
              locations: cross-substrate ref format per CONVENTIONS §5.
            — BUSINESS consumes Route.total_distance_m for logistics
              cost computation.
            — BUSINESS consumes ServiceArea.resulting_geometry for
              delivery zone eligibility checking.
            — BUSINESS Organization.locations[] references SPATIAL
              Location for multi-location management.
          Ownership: SPATIAL owns geographic data (Address, Location,
          Route, ServiceArea). BUSINESS owns commercial context (billing
          vs shipping, pricing, service level).
          Events: substrate.spatial.route.computed (BUSINESS consumes
          for logistics), substrate.spatial.service_area.computed
          (BUSINESS consumes for eligibility).

INT-S004: SPATIAL ↔ DESIGN — Site Planning
          Protocol:
            — DESIGN requests site context: SPATIAL returns
              SpatialFeatures within site vicinity, applicable
              SpatialConstraints (setbacks, flood zones, utility
              corridors), and terrain data (Raster DEM).
            — DESIGN Geometry (TERM-D006, artifact shape in local coords)
              links to SPATIAL SpatialGeometry (TERM-S004, site position
              in Earth coords) via shared entity_id.
            — For BIM: DESIGN owns IFC building model geometry; SPATIAL
              owns site footprint on cadastral map.
          Ownership: DESIGN owns artifact specification. SPATIAL owns
          geographic placement and site context.
          Mirror: INT-D009 in SUBSTRATE-DESIGN.

INT-S005: SPATIAL ↔ GOVERNANCE — Jurisdiction & Zoning
          Protocol:
            — GOVERNANCE Jurisdiction.geographic_extent_ref →
              SPATIAL Zone (zone_type: administrative).
            — SPATIAL Zone boundary changes emit substrate.spatial.zone
              .boundary_modified; GOVERNANCE updates Jurisdiction scope.
            — GOVERNANCE Norm references SPATIAL Zone for spatial scope
              of normative applicability.
            — Zoning violations: SPATIAL evaluates feature-in-zone
              relationship; emits substrate.spatial.constraint.violated;
              GOVERNANCE evaluates norm violation and determines
              consequences.
          Ownership: GOVERNANCE owns normative meaning (what is
          permitted). SPATIAL owns boundary geometry (where it applies).
          Principle P3 (Define vs Enforce).
          Mirror: INT-G009 in SUBSTRATE-GOVERNANCE.

INT-S006: SPATIAL ↔ PHYSICAL — Location & Sensing
          Protocol:
            — PHYSICAL emits substrate.physical.measurement.recorded
              with GPS/GNSS position data; SPATIAL creates/updates
              Location (ENT-S002).
            — PHYSICAL PhysicalAsset.location_ref → SPATIAL Location.
            — PHYSICAL emits substrate.physical.asset.relocated; SPATIAL
              updates Location and Trajectory.
            — PHYSICAL Zone (TERM-P018, operational safety grouping)
              MAY reference SPATIAL Zone (TERM-S016) for geographic
              positioning of the facility containing the PHYSICAL zone.
          Ownership: PHYSICAL owns measurement hardware and raw sensor
          data. SPATIAL owns geographic interpretation and position
          history.
          Mirror: INT-P009 in SUBSTRATE-PHYSICAL.

INT-S007: SPATIAL ↔ KNOWLEDGE — Geographic Provenance
          Protocol:
            — KNOWLEDGE Source (TERM-K020) and Observation (TERM-K019)
              MAY carry location_ref → SPATIAL Location for geographic
              provenance.
            — SpatialAccuracy (TERM-S029) MAY link to KNOWLEDGE
              Proposition for accuracy claims entering the epistemic
              record.
          Ownership: KNOWLEDGE owns epistemic structure (what is known,
          with what confidence). SPATIAL owns geographic vocabulary
          (where it was observed/measured).

INT-S008: SPATIAL ↔ COMMUNICATION — Geographic Context
          Protocol:
            — COMMUNICATION Discourse context MAY reference SPATIAL
              Zone or Place for geographic scoping of discussions.
            — When discourse has geographic relevance (local government
              meeting, site-specific negotiation), SPATIAL provides
              geographic context references.
          Ownership: COMMUNICATION owns discourse structure. SPATIAL
          owns geographic context entities.
```

---

## 9. AUTHORIZATION & ACCESS MODEL

> Resource identifiers follow the pattern RES-S###. The permission
> matrix maps actors to resources with permitted operations.

```
RES-S001: CoordinateReferenceSystem — register, read, deprecate
RES-S002: Location — create, read, update, invalidate
RES-S003: Address — create, read, update, geocode, reverse_geocode
RES-S004: SpatialGeometry — create, read, validate
RES-S005: SpatialFeature — create, read, update, archive, supersede
RES-S006: Layer — create, read, update, archive
RES-S007: SpatialDataset — create, read, publish, archive
RES-S008: Raster — create, read, archive
RES-S009: SpatialRelationship — compute, read
RES-S010: SpatialConstraint — create, read, update, suspend, retire
RES-S011: SpatialIndex — create, read, rebuild
RES-S012: SpatialNetwork — create, read, update, archive
RES-S013: NetworkSegment — create, read, update, close
RES-S014: Route — compute, read, activate, invalidate
RES-S015: ServiceArea — compute, read
RES-S016: Zone — create, read, modify_boundary, modify_rules, suspend,
          dissolve
RES-S017: Territory — create, read, assign, rebalance, dissolve
RES-S018: Boundary — create, read, update, dissolve
RES-S019: Place — create, read, update, archive
RES-S020: GeocodingResult — create (system), read, select_candidate
RES-S021: Trajectory — start, append, complete, read, simplify
RES-S022: Coverage — compute, read
RES-S023: Density — compute, read
RES-S024: ProximityRule — create, read, update, pause, expire
RES-S025: Floor — create, read, update, archive
RES-S026: IndoorSpace — create, read, update, archive
RES-S027: SpatialEnvelope — create, read, update, suspend, revoke
RES-S028: SpatialPolicy — create, read, update, suspend, retire
RES-S029: SpatialAccuracy — create, read (immutable after creation)

Permission Matrix (summary — full matrix per implementation):

  ACT-S001 (Analyst):   RES-S001–S029 read; RES-S002–S005 create/update;
                         RES-S009 compute; RES-S014–S015 compute;
                         RES-S021 start/append/complete; RES-S022–S023
                         compute; RES-S024 create/update.
  ACT-S002 (Steward):   All RES-S001–S029 all operations. Full authority
                         over spatial configuration, policy, and data
                         lifecycle.
  ACT-S003 (AI Narrow): RES-S002–S003 read; RES-S014 compute; RES-S015
                         compute; RES-S009 compute; RES-S020 read/select.
                         Bound by SpatialEnvelope (TERM-S027).
  ACT-S004 (AI General):ACT-S003 permissions plus: RES-S016 create/
                         modify_boundary; RES-S017 assign/rebalance;
                         RES-S005 create/update. Bound by expanded
                         SpatialEnvelope.
  ACT-S005 (Internal):  RES-S001–S029 read (at full precision); RES-S014
                         compute; RES-S020 select_candidate.
  ACT-S006 (External):  RES-S002 create (GPS feeds); RES-S021 append
                         (position feeds); RES-S005 read (filtered by
                         SpatialPolicy access). Write access limited to
                         authorized datasets.
  ACT-S007 (Auditor):   RES-S001–S029 read (all data including audit
                         logs). No write/modify permissions.
  ACT-S008 (Ext User):  RES-S014 compute (rate-limited); RES-S020 read
                         (degraded precision); RES-S016 read (public
                         zones only); RES-S019 read. Precision degraded
                         per SpatialPolicy resolution type.
```

---

## 10. SECURITY & PRIVACY MODEL

> Classification identifiers follow CLASS-S###. Threat identifiers
> follow THREAT-S###. Abuse pattern identifiers follow ABUSE-S###.

```
CLASS-S001: Location data — SENSITIVE
            Location coordinates, trajectories, and geocoding results
            are PII under GDPR Article 4(1), CCPA 1798.140(o), and
            sector regulations (HIPAA, COPPA, FERPA). Precise location
            reveals medical visits, religious practice, political
            affiliation, romantic relationships, substance use patterns,
            income level, and immigration status. ASM-S010.

CLASS-S002: Spatial feature data — STANDARD to SENSITIVE
            Depends on feature type. Building footprints: STANDARD
            (public record). Person locations: SENSITIVE. Vehicle
            positions: SENSITIVE (reveals driver behavior). Parcel
            boundaries: STANDARD (cadastral public record). Military
            facility features: RESTRICTED.

CLASS-S003: Route data — STANDARD to SENSITIVE
            Route computations for public directions: STANDARD.
            Route data revealing habitual travel patterns: SENSITIVE.
            Routes for high-value transport (cash in transit, hazmat):
            RESTRICTED.

CLASS-S004: Zone and boundary data — STANDARD
            Administrative boundaries, zoning data, and public zone
            information are generally public record. Exception: military
            zone boundaries, classified facility perimeters.

CLASS-S005: Geocoding audit trail — SENSITIVE
            Geocoding results reveal what addresses users searched for.
            Aggregated geocoding queries reveal organizational interest
            in specific locations (site selection, competitive analysis).

CLASS-S006: Indoor spatial data — SENSITIVE
            Floor plans, room layouts, and indoor positioning data reveal
            building security architecture. Occupancy data reveals
            organizational structure and work patterns.

THREAT-S001: Location tracking via geocoding queries
             Threat: Adversary monitors geocoding requests to track an
             individual's movements or interests.
             Mitigation: SpatialPolicy privacy rules. Rate limiting per
             actor. Geocoding query logs access-controlled.

THREAT-S002: Spatial data poisoning
             Threat: Adversary submits false spatial features or
             positions to corrupt routing, coverage analysis, or zone
             compliance.
             Mitigation: Source validation (ACT-S006 authenticated).
             Accuracy metadata verification. Anomaly detection on
             position feeds (speed/distance plausibility checks).

THREAT-S003: Boundary manipulation for regulatory arbitrage
             Threat: Actor modifies Zone boundaries to place entities
             in/out of regulatory zones for compliance avoidance.
             Mitigation: Zone boundary modifications require ACT-S002
             authority. All boundary changes logged with rationale.
             GOVERNANCE receives boundary change events for compliance
             re-evaluation.

THREAT-S004: Precision reconstruction from degraded data
             Threat: Adversary combines multiple degraded-precision
             location queries to reconstruct precise location.
             Mitigation: SpatialPolicy differential_privacy_epsilon
             provides mathematical privacy guarantee. Spatial cloaking
             radius applies consistent noise. K-anonymity ensures
             minimum group size.

THREAT-S005: Route inference from timing data
             Threat: Adversary infers route and destination from
             departure time and arrival time without direct route access.
             Mitigation: Temporal cloaking (SpatialPolicy temporal_
             cloaking_window_s). Route data access controls.

THREAT-S006: Indoor surveillance via occupancy data
             Threat: Adversary uses indoor space occupancy and
             positioning data to monitor individual movements within
             buildings.
             Mitigation: IndoorSpace occupancy data classified SENSITIVE.
             Individual indoor positions require explicit consent.
             Aggregate occupancy (room is "occupied" vs "available")
             is lower sensitivity than individual tracking.

ABUSE-S001: Mass location surveillance
            Pattern: Actor with broad spatial access systematically
            queries locations of many individuals for profiling.
            Detection: Query volume monitoring per actor. Alert on
            bulk trajectory queries. Rate limiting on person_location
            feature queries. Audit log review by ACT-S007.

ABUSE-S002: Territory gerrymandering
            Pattern: AI agent rebalances Territories to disadvantage
            certain populations or assignees.
            Detection: Territory assignment fairness audit. Performance
            metric distribution analysis. Demographic impact assessment
            of territory boundaries. ACT-S007 review.

ABUSE-S003: Geocoding weaponization
            Pattern: Actor uses geocoding to identify physical locations
            of individuals for harassment or targeting.
            Detection: Geocoding query pattern analysis. Correlation
            between geocoding queries and person_location features.
            Rate limiting on reverse geocoding of residential addresses.
```

---

## 11. BEHAVIORAL CONTRACTS

> Invariant identifiers: INV-S###. Precondition identifiers: PRE-S###.
> Postcondition identifiers: POST-S###. Forbidden action identifiers:
> FORBID-S###. Failure mode identifiers: FAIL-S###.

### 11.1 Invariants

```
INV-S001: Every Location MUST have accuracy metadata
          (SpatialAccuracy ref or inline accuracy fields). A Location
          without accuracy information MUST NOT be persisted.

INV-S002: All coordinate storage MUST be in WGS84 (EPSG:4326). No
          entity may store coordinates in a non-WGS84 CRS as primary
          storage. Display and computation CRS are secondary.

INV-S003: Every geocoding operation MUST produce a GeocodingResult
          with candidates[]. Single-point geocoding without confidence
          score is forbidden.

INV-S004: Accuracy MUST NOT silently improve through computation. The
          output accuracy of any spatial operation is at most as good as
          its least-accurate input.

INV-S005: SpatialPolicy precision degradation MUST be irreversible at
          the API boundary. A consumer receiving neighborhood-level data
          MUST NOT be able to reconstruct exact coordinates from the
          response.

INV-S006: Published SpatialDataset versions MUST be immutable. No
          entity within a published dataset may be modified. Changes
          produce a new version.

INV-S007: Every SpatialFeature MUST have temporal_validity. Features
          without validity periods MUST NOT be persisted.

INV-S008: Every AI agent spatial operation MUST be checked against
          SpatialEnvelope before execution. No spatial operation may
          bypass envelope validation.

INV-S009: Every Zone boundary modification MUST be logged with actor,
          rationale, and timestamp. Boundary changes without audit
          trail are forbidden.

INV-S010: Route validity_window MUST be assigned at computation time.
          Routes without validity windows MUST NOT be cached or served.

INV-S011: SpatialChange cascade analysis MUST identify all affected
          downstream entities. Cascade analysis that misses affected
          Routes, ServiceAreas, or Coverages is a system error.

INV-S012: Cross-substrate references to SPATIAL entities MUST be
          read-only from the consumer side. No peer substrate may
          modify a SPATIAL entity through a cross-substrate reference.
```

### 11.2 Preconditions

```
PRE-S001: Before creating a SpatialFeature, the SpatialGeometry MUST
          be valid per OGC Simple Features (no self-intersections,
          correct ring orientation).

PRE-S002: Before computing a Route, origin and destination Locations
          MUST be resolved (not ambiguous geocoding results). If
          addresses are provided, geocoding MUST complete first.

PRE-S003: Before modifying a Zone boundary, the actor MUST have
          zone_modification_authority (ACT-S002 or ACT-S004 with
          envelope permission).

PRE-S004: Before Territory rebalancing, all rebalancing_constraints
          MUST be specified (minimize_disruption, maintain_contiguity,
          max_reassignment_pct).

PRE-S005: Before serving spatial data to external actors (ACT-S006,
          ACT-S008), SpatialPolicy precision degradation MUST be
          applied.

PRE-S006: Before computing Coverage, the target_area geometry MUST be
          valid and the resource locations MUST have accuracy metadata.
```

### 11.3 Postconditions

```
POST-S001: After creating a SpatialFeature, the feature MUST be
           indexed in the SpatialIndex at configured resolutions.

POST-S002: After computing a Route, the Route MUST have total_distance_m,
           estimated_duration_s, validity_window, and accuracy_ref.

POST-S003: After detecting a SpatialChange, cascade_analysis MUST be
           computed and substrate.spatial.change.detected MUST be
           emitted.

POST-S004: After geocoding, GeocodingResult MUST contain at least one
           candidate or be in failed state with reason.

POST-S005: After Territory rebalancing, all territories MUST satisfy
           maintain_contiguity constraint (if specified) and total
           coverage of parent Zone MUST be preserved.

POST-S006: After Zone boundary modification, all SpatialConstraints
           referencing that Zone MUST be re-evaluated, and affected
           GOVERNANCE Jurisdictions MUST receive boundary_modified event.
```

### 11.4 Forbidden Actions

```
FORBID-S001: MUST NOT store coordinates in non-WGS84 CRS as primary
             storage.

FORBID-S002: MUST NOT serve geocoding results without confidence scores
             and candidate lists.

FORBID-S003: MUST NOT silently upgrade accuracy through computation
             (e.g., reporting survey-grade accuracy for a result derived
             from GPS-grade inputs).

FORBID-S004: MUST NOT allow AI agents to operate outside SpatialEnvelope
             bounds, even if role-based permissions would permit it.

FORBID-S005: MUST NOT expose exact coordinates to actors whose
             SpatialPolicy specifies degraded precision.

FORBID-S006: MUST NOT modify published SpatialDataset versions.

FORBID-S007: MUST NOT delete spatial data under retention policy hold.

FORBID-S008: MUST NOT create Routes without validity_window.

FORBID-S009: MUST NOT allow Zone boundary modification without audit
             trail.

FORBID-S010: MUST NOT process SpatialChange without computing cascade
             analysis.

FORBID-S011: MUST NOT store trajectory data beyond SpatialPolicy
             retention period without explicit retention extension.

FORBID-S012: MUST NOT allow cross-substrate write access to SPATIAL
             entities. Peer substrates reference SPATIAL entities as
             read-only.
```

### 11.5 Failure Modes

```
FAIL-S001: CRS transform error — requested transform between
           incompatible or unsupported CRS. Response: reject operation,
           return error with supported CRS list.

FAIL-S002: Geometry validation failure — submitted geometry fails OGC
           Simple Features validation. Response: reject with
           validation_errors[], suggest correction.

FAIL-S003: Geocoding failure — no candidates match input address.
           Response: return GeocodingResult in failed state with
           reason (no match, input too vague, country not supported).

FAIL-S004: Route computation infeasible — no path exists between origin
           and destination in the selected network (disconnected graph,
           all segments closed). Response: return infeasibility report
           with closest reachable point.

FAIL-S005: SpatialEnvelope violation — AI agent requests operation
           outside authorized geographic scope or without required
           authority. Response: block operation, log violation, return
           error with envelope bounds.

FAIL-S006: Accuracy threshold breach — spatial data accuracy below
           SpatialPolicy quality minimum for the requested operation.
           Response: warn or reject (per policy enforcement level).

FAIL-S007: Spatial index unavailable — query requires spatial index
           that has not been built or is being rebuilt. Response: fall
           back to sequential scan (with performance warning) or queue
           for execution after index rebuild.

FAIL-S008: SpatialChange cascade overflow — cascade analysis identifies
           more affected entities than configurable threshold. Response:
           partial cascade with overflow flag, human review required for
           complete assessment.
```

---

## 12. DECISION POINTS

> Decision point identifiers follow the pattern DEC-S###. Each
> decision point identifies a situation requiring human judgment or
> explicit policy configuration.

```
DEC-S001: CRS Selection for Computation
          When: A spatial computation (area, distance, overlay) requires
          a projected CRS for accuracy (geodetic lat/lon is inadequate
          for metric operations over large areas).
          Options: UTM zone (local accuracy, zone-dependent), Albers
          equal-area (area-preserving), Lambert conformal conic (angle-
          preserving), Web Mercator (display, not computation).
          Decision owner: ACT-S002 (Steward) configures default CRS
          per operation type and geographic region.
          Fallback: UTM zone of the operation's centroid.

DEC-S002: Geocoding Candidate Selection
          When: GeocodingResult has multiple candidates with similar
          confidence scores (ambiguity_flag = true).
          Options: Select highest confidence (automatic), present to
          user for selection, apply organizational policy default (prefer
          local addresses), defer until additional context available.
          Decision owner: ACT-S001 or ACT-S005 (human selection),
          ACT-S003 (AI selection within envelope authority).
          Fallback: Highest confidence candidate if no selection within
          configurable timeout.

DEC-S003: Routing Algorithm Selection
          When: Route computation must balance speed, accuracy, and
          constraint complexity.
          Options: Dijkstra (exact, slow for large networks), A* (fast,
          good heuristic), Contraction Hierarchies (fastest for static
          networks, expensive precomputation), custom solver for VRP.
          Decision owner: Delegated to COMPUTE Pipeline (INT-S002).
          SPATIAL defines problem; solver selection is implementation.
          Fallback: A* with geodesic heuristic.

DEC-S004: Zone Boundary Dispute Handling
          When: Boundary.disputed = true and a spatial query depends on
          which boundary interpretation to use.
          Options: Use organizational default (configured per Zone), use
          requesting user's jurisdiction preference, return all variants
          with flag, reject query requiring disputed boundary resolution.
          Decision owner: ACT-S002 (organizational policy), ultimately
          external political resolution.
          Fallback: Return all boundary variants with disputed flag.

DEC-S005: Spatial Precision vs Privacy
          When: Actor's analytical need requires higher precision than
          SpatialPolicy permits for the data subject.
          Options: Deny access, provide degraded precision with
          analytical limitations noted, require explicit consent from
          data subject, provide aggregate/anonymized data instead.
          Decision owner: ACT-S002 (policy), data subject (consent).
          Fallback: Enforce SpatialPolicy — provide degraded precision.

DEC-S006: Coverage Gap Response
          When: Coverage analysis reveals gaps below regulatory standard.
          Options: Alert operations team, automatically generate
          facility placement recommendations (via COMPUTE), escalate to
          GOVERNANCE for compliance reporting, defer to next scheduled
          review.
          Decision owner: ACT-S002 (operational), ACT-S004 (optimization).
          Fallback: Alert and log; automated placement is SHOULD, not
          MUST.
```

---

## 13. CONCURRENCY & ORDERING

> Concurrency identifiers follow the pattern CONC-S###.

```
CONC-S001: Spatial Feature Update Conflict Resolution
           When two actors modify the same SpatialFeature concurrently
           (e.g., two GPS feeds updating the same asset's position):
           — Strategy: Last-write-wins for position updates (most recent
             timestamp prevails). Optimistic concurrency (version check)
             for property and geometry modifications.
           — For position updates: compare timestamps; most recent
             Location with valid accuracy metadata wins.
           — For geometry/property modifications: check version; reject
             if version has advanced since read. Retry with fresh read.
           — Spatial-temporal versioning: each version carries both a
             version number and a valid_from timestamp. Historical
             queries use temporal_validity, not version order alone.

CONC-S002: Route Computation During Network Change
           When a SpatialChange modifies the network while routes are
           being computed:
           — Strategy: Routes computed against a network snapshot.
             validity_window reflects the snapshot time. If SpatialChange
             arrives during computation, the route is still valid for its
             snapshot but may be immediately invalidated upon publication.
           — Ordering: SpatialChange events are ordered by
             effective_datetime. Route invalidation processes changes in
             order.

CONC-S003: Zone Boundary Modification Ordering
           When multiple Zone boundary modifications affect overlapping
           areas:
           — Strategy: Serialize boundary modifications per Zone. Allow
             concurrent modifications to non-overlapping Zones. Detect
             overlap conflicts (two zones claiming the same area when
             hierarchy rules forbid overlap) and reject the later
             modification.
           — Events: boundary_modified events carry a monotonic sequence
             number per Zone for ordering.

CONC-S004: Geocoding Result Selection Race
           When multiple actors attempt to select different candidates
           for the same GeocodingResult:
           — Strategy: First selection wins. Subsequent selections are
             rejected with "already resolved" error and the selected
             candidate is returned. If override is needed, a new
             GeocodingResult must be requested.

CONC-S005: Trajectory Position Append Ordering
           When position updates for the same Trajectory arrive out of
           order (network delay, multi-sensor):
           — Strategy: Order by position timestamp, not arrival time.
             Late-arriving positions are inserted at the correct temporal
             position. Dwell point and distance computations are
             recalculated on insertion of out-of-order positions.
```

---

## 14. ERROR HANDLING & RECOVERY

> Error identifiers follow the pattern ERR-S###.

```
ERR-S001: Invalid coordinates — latitude outside [-90, +90] or
          longitude outside [-180, +180].
          Recovery: reject with error; do not attempt correction.

ERR-S002: Invalid geometry — OGC Simple Features validation failure.
          Recovery: reject with validation_errors[]. System MAY suggest
          auto-repair (remove self-intersections, fix ring orientation)
          but MUST NOT auto-repair without actor consent.

ERR-S003: CRS not registered — requested EPSG code not in system.
          Recovery: reject with error; provide list of supported CRS.

ERR-S004: CRS transform failure — incompatible datums or missing
          transform parameters.
          Recovery: reject with error; suggest compatible CRS pair.

ERR-S005: Geocoding no results — address text matches nothing.
          Recovery: return GeocodingResult(failed) with reason. Suggest
          relaxed query (remove unit number, try broader area).

ERR-S006: Geocoding service unavailable — external geocoding backend
          down.
          Recovery: return cached result if available (with staleness
          warning). If no cache: return error with retry suggestion.

ERR-S007: Route computation timeout — solver exceeds time limit.
          Recovery: return best solution found so far with optimality_
          gap. Or return error with suggestion to simplify (fewer
          waypoints, smaller network).

ERR-S008: Route network disconnected — no path between origin and
          destination.
          Recovery: return closest reachable point from origin toward
          destination with remaining straight-line distance.

ERR-S009: Feature schema violation — SpatialFeature properties do not
          match Layer feature_schema.
          Recovery: reject with schema violation details. List required
          and missing properties.

ERR-S010: Accuracy below threshold — spatial data accuracy worse than
          SpatialPolicy quality minimum.
          Recovery: warn (soft policy) or reject (hard policy) with
          required vs actual accuracy.

ERR-S011: SpatialEnvelope violation — AI agent operation outside
          authorized scope.
          Recovery: block operation; log violation; return envelope
          bounds and required authority.

ERR-S012: Dataset version conflict — attempt to modify published
          dataset.
          Recovery: reject; instruct to create new version.

ERR-S013: Retention policy violation — attempt to delete data under
          hold.
          Recovery: reject; return retention policy details and
          earliest deletion date.

ERR-S014: SpatialIndex rebuild in progress — query requires index
          currently being rebuilt.
          Recovery: queue query for post-rebuild execution or fall back
          to sequential scan with performance warning.

ERR-S015: ProximityRule target geometry invalid — geofence polygon
          self-intersects or exceeds maximum vertex count.
          Recovery: reject with geometry validation errors. Suggest
          simplification.

ERR-S016: Territory rebalancing infeasible — constraints
          (maintain_contiguity + max_reassignment_pct) cannot be
          simultaneously satisfied.
          Recovery: report constraint conflict. Suggest relaxing
          max_reassignment_pct or allowing non-contiguous territories.

ERR-S017: Indoor routing failure — no path between origin and
          destination indoor spaces (disconnected floor plan, missing
          vertical connections).
          Recovery: report missing connection. Suggest nearest
          alternative destination with valid path.

ERR-S018: SpatialChange cascade overflow — affected entities exceed
          configurable threshold.
          Recovery: compute partial cascade (up to threshold). Flag
          overflow. Require human review for complete assessment.
```

---

## 15. PERSISTENCE REQUIREMENTS

> Persistence identifiers follow the pattern PERS-S###.

```
PERS-S001: Event Store
           All spatial state changes persisted as immutable events.
           Event ordering: per-entity monotonic sequence number plus
           global approximate timestamp. Event schema includes: event_id,
           entity_type, entity_id, event_type, payload, actor_ref,
           timestamp, spatial_accuracy_ref, crs_ref. Retention: events
           retained per entity retention policy (PERS-S003). Event store
           must support: temporal projection (state at time T), entity
           history (all events for entity E), spatial-temporal query
           (events within area A during time range T1-T2).

PERS-S002: Spatial Index Store
           Spatial indexes (H3, S2, R-tree) persisted separately from
           event store for query performance. Indexes are derived state
           — rebuildable from events. Index update latency: ≤ projection
           latency bound (OPS-S001). Index store must support: cell
           lookup (Location → cell_id), range query (all features in
           cell set), nearest neighbor.

PERS-S003: Retention Policies (per SpatialPolicy retention type)
           — Cadastral features: 100+ years (legal property records).
           — Road network features: 10+ years (transportation planning).
           — Building features: 50+ years (urban development history).
           — Administrative zone boundaries: indefinite (historical
             governance records).
           — Fleet positions / trajectory data: 90 days default
             (configurable per SpatialPolicy).
           — Route computations: 30 days (cache, not permanent record).
           — ProximityRule trigger events: 30 days default.
           — GeocodingResult audit trail: 1 year default.
           — SpatialChange events: 10 years (infrastructure change
             history).
           All retention periods configurable per SpatialPolicy. Deletion
           must be verifiable and logged.

PERS-S004: Backup & Recovery
           — Spatial event store: continuous replication. RPO ≤ 1 minute.
             RTO ≤ 15 minutes.
           — Spatial index store: rebuild from events if lost. Rebuild
             time depends on feature count (estimate: 1M features/minute).
           — Raster data: separate backup cadence (large binary data).
             RPO ≤ 1 hour. RTO ≤ 1 hour.
           — Cross-substrate references: SPATIAL entities referenced by
             peer substrates must survive backup/restore with consistent
             IDs (UUID stability).
```

---

## 16. MIGRATION & ONBOARDING

> Onboarding identifiers follow the pattern ONBOARD-S###.

```
ONBOARD-S001: Shapefile / GeoJSON Import
              Input: ESRI Shapefile (.shp/.dbf/.shx/.prj) or GeoJSON
              (RFC 7946) files.
              Process: Parse geometry and properties. Validate geometry
              (OGC Simple Features). Read CRS from .prj or GeoJSON
              (default WGS84). Transform to WGS84 if needed. Create
              SpatialFeatures with properties mapped to Layer
              feature_schema. Assign SpatialAccuracy based on source
              metadata (if available) or default (digitized).
              Output: SpatialFeatures in Layer within SpatialDataset.

ONBOARD-S002: PostGIS / Spatial Database Import
              Input: PostGIS tables with geometry columns.
              Process: Read geometry type and SRID. Transform to WGS84.
              Map columns to SpatialFeature properties per Layer
              feature_schema. Import spatial indexes if compatible.
              Validate geometry. Create SpatialFeatures.
              Output: Layer with features, preserving spatial relationships.

ONBOARD-S003: ArcGIS Feature Service Import
              Input: ArcGIS REST Feature Service endpoint.
              Process: Query features with pagination. Convert Esri JSON
              geometry to GeoJSON/WKB. Map fields to properties.
              Transform from service CRS to WGS84. Create SpatialFeatures.
              Output: Layer with features.

ONBOARD-S004: Google Maps / Mapping Platform Import
              Input: Google Maps Platform exports (KML, GeoJSON), Mapbox
              datasets, HERE data exports.
              Process: Parse platform-specific format. Extract geometry
              and properties. Transform CRS. Create SpatialFeatures and
              Places.
              Output: SpatialFeatures and Places with mapping platform
              attribution in source_ref.

ONBOARD-S005: OpenStreetMap Import
              Input: OSM PBF or XML file (planet file or regional extract).
              Process: Parse nodes, ways, relations. Convert to
              SpatialFeatures with OSM tags mapped to properties. Build
              SpatialNetwork from highway=* tagged ways. Create Places
              from name=* tagged features. Assign accuracy: digitized
              (community-sourced data, typical accuracy 5-20m).
              Output: SpatialFeatures, SpatialNetwork, Places from OSM.

ONBOARD-S006: Indoor Maps / IFC Import
              Input: IFC (Industry Foundation Classes) BIM file, IMDF
              (Indoor Mapping Data Format), IndoorGML.
              Process: Parse floor/space structure. Create Floors from
              IfcBuildingStorey. Create IndoorSpaces from IfcSpace.
              Extract connectivity from door/opening relationships.
              Map building to SpatialFeature (building footprint).
              Assign SpatialAccuracy: survey_grade for IFC (typically
              ±5cm).
              Output: Floors, IndoorSpaces with connectivity graph,
              building SpatialFeature.
```

---

## 17. OPERATIONAL PROFILE

> Operational identifiers follow the pattern OPS-S###.

```
OPS-S001: Performance Envelope
          — Tier 1 operations (point-in-polygon, proximity check, feature
            lookup, geocoding): P95 latency ≤ 100ms.
          — Tier 2 operations (single route computation, service area,
            spatial join): P95 latency ≤ 1s.
          — Tier 3 operations (coverage analysis, territory optimization,
            route matrix): P95 latency ≤ 60s.
          — Tier 4 operations (global optimization, dataset migration):
            unbounded, delegated to COMPUTE Pipeline.
          — Event projection latency (event to queryable state):
            P95 ≤ 500ms.
          — ProximityRule evaluation latency (position update to trigger):
            P95 ≤ 200ms.

OPS-S002: Throughput Envelope
          — Geocoding: ≤ 10,000 requests/second per instance.
          — Routing: ≤ 1,000 single-route computations/second per
            instance.
          — Feature queries: ≤ 50,000 spatial queries/second per
            instance.
          — Position ingestion (fleet/IoT): ≤ 100,000 positions/second
            per instance.
          — ProximityRule evaluations: ≤ 50,000 evaluations/second per
            instance.
          — Total global capacity: 50B queries/day (ASM-S009) across
            all instances.

OPS-S003: Availability & Degradation
          — Target availability: 99.95% for Tier 1-2 operations.
          — Degradation hierarchy: if spatial index unavailable, fall
            back to sequential scan (degraded performance, correct
            results). If routing network unavailable, return
            straight-line distance with warning. If geocoding backend
            unavailable, return cached results with staleness flag.
          — Circuit breaker: if COMPUTE solver is unavailable, queue
            Tier 3-4 operations with estimated processing time.
          — Health check: system MUST expose spatial index health,
            geocoding backend reachability, routing network freshness,
            and event projection lag as operational metrics.
```

---

## 18. TEST PLAN

> Test identifiers follow the pattern TEST-S###.

```
TEST-S001: CRS registration and coordinate storage in WGS84.
TEST-S002: CRS transform accuracy (WGS84 ↔ UTM, WGS84 ↔ NAD83,
           WGS84 ↔ Web Mercator) within documented error bounds.
TEST-S003: Location creation with mandatory accuracy metadata.
TEST-S004: Location validation (latitude/longitude range checks).
TEST-S005: Address creation with multiple addressing systems.
TEST-S006: Forward geocoding produces GeocodingResult with ranked
           candidates and confidence scores.
TEST-S007: Reverse geocoding produces nearest Address with distance.
TEST-S008: Geocoding ambiguity correctly flagged when multiple
           candidates have confidence > 0.5.
TEST-S009: SpatialGeometry validation (OGC Simple Features compliance).
TEST-S010: SpatialGeometry area/length/centroid computation accuracy
           (geodesic vs projected).
TEST-S011: SpatialFeature lifecycle (SM-S001: draft → active → archived
           | superseded).
TEST-S012: Layer feature_schema enforcement on feature creation.
TEST-S013: SpatialDataset versioning and immutability of published
           versions.
TEST-S014: All DE-9IM topological predicates (contains, within,
           intersects, overlaps, touches, crosses, disjoint, equals,
           covers, covered_by).
TEST-S015: Metric relationships (within_distance, nearest_k) with
           geodesic, euclidean, and network metrics.
TEST-S016: SpatialConstraint evaluation with hard/soft/preference
           levels and relaxation ordering.
TEST-S017: SpatialIndex cell_id lookup at all supported resolutions.
TEST-S018: Route computation (single origin-destination) with multiple
           optimization criteria.
TEST-S019: Route with waypoints (ordered intermediate stops).
TEST-S020: Route with vehicle_profile constraints (height/weight/hazmat).
TEST-S021: Route invalidation on SpatialChange affecting segments.
TEST-S022: ServiceArea computation (isochrone, isodistance, isocost)
           with contour intervals.
TEST-S023: Zone creation, nesting, and point-in-zone queries.
TEST-S024: Zone lifecycle (SM-S003: proposed → active → suspended |
           dissolved).
TEST-S025: Territory assignment, performance metrics, and rebalancing.
TEST-S026: Boundary creation with crossing rules and disputed flag.
TEST-S027: Place creation with multilingual naming and hierarchy.
TEST-S028: Trajectory recording, dwell point detection, and
           simplification.
TEST-S029: Trajectory privacy (spatial cloaking, temporal cloaking).
TEST-S030: Coverage computation with gap identification and regulatory
           standard checking.
TEST-S031: Density computation (kernel density estimation and grid
           count).
TEST-S032: ProximityRule creation and trigger evaluation (enter/exit/
           both).
TEST-S033: ProximityRule cooldown and active_window enforcement.
TEST-S034: Floor and IndoorSpace creation with connectivity graph.
TEST-S035: Indoor routing across floors via vertical connections.
TEST-S036: SpatialEnvelope enforcement (geographic scope, authority
           limits).
TEST-S037: SpatialPolicy precision degradation at API boundary.
TEST-S038: SpatialPolicy privacy (k-anonymity, spatial cloaking).
TEST-S039: SpatialChange cascade analysis (road closure invalidating
           Routes, ServiceAreas, Coverages).
TEST-S040: Cross-substrate integration: TEMPORAL travel duration
           resolution via INT-S001 (Route duration consumed by
           TransitionTime).
```

---

## 19. OBSERVABILITY & AUDITABILITY

> Log identifiers: LOG-S###. Metric identifiers: MET-S###. Alert
> identifiers: ALERT-S###.

### 19.1 Structured Logs

```
LOG-S001: Feature lifecycle events — creation, update, archive,
          supersede. Includes: feature_id, feature_type, actor_ref,
          geometry_hash (for change detection without storing full
          geometry in log), accuracy_ref, timestamp.

LOG-S002: Geocoding decisions — forward/reverse geocoding requests,
          candidate lists, selection decisions. Includes: input,
          candidate_count, selected_candidate, confidence, actor_ref,
          selection_method.

LOG-S003: Route computations — origin, destination, optimization
          criterion, solver used, computation_time_ms, result (distance,
          duration, segment_count). Includes: route_id, network_ref,
          vehicle_profile, actor_ref.

LOG-S004: Zone boundary modifications — old geometry hash, new geometry
          hash, modification reason, actor_ref, approval chain.

LOG-S005: SpatialEnvelope violations — agent_ref, requested operation,
          envelope bounds, violation type (geographic scope, authority,
          accuracy threshold).

LOG-S006: SpatialPolicy enforcement — precision degradation applied,
          actor_ref, original precision, degraded precision, policy_ref.

LOG-S007: SpatialChange events — change_type, affected_area,
          cascade_analysis summary, severity, source_ref.

LOG-S008: ProximityRule triggers — rule_id, source_entity position,
          target_geometry, distance_at_trigger, trigger_action,
          timestamp.

LOG-S009: Cross-substrate interactions — integration contract ref,
          peer substrate, operation, payload summary, response time_ms.
```

### 19.2 Metrics

```
MET-S001: Geocoding requests/second (by result_type, confidence range).
MET-S002: Geocoding latency P50/P95/P99 (by input type).
MET-S003: Route computations/second (by network_type, optimization).
MET-S004: Route computation latency P50/P95/P99.
MET-S005: Spatial queries/second (by query type: point-in-polygon,
          within_distance, nearest_k, feature_lookup).
MET-S006: Event projection lag (event timestamp to queryable state).
MET-S007: SpatialIndex query latency (by index type, resolution).
MET-S008: ProximityRule evaluation latency (position update to trigger).
MET-S009: SpatialChange cascade size (affected entities per change).
MET-S010: Accuracy distribution (histogram of SpatialAccuracy.
          horizontal_accuracy_m across all active features).
MET-S011: Geocoding ambiguity rate (percentage of results with
          ambiguity_flag = true).
MET-S012: Route invalidation rate (routes invalidated per day).
MET-S013: Coverage gap percentage (per coverage analysis, tracked over
          time).
MET-S014: SpatialEnvelope violation rate (violations per agent per day).
```

### 19.3 Alerts

```
ALERT-S001: Geocoding ambiguity rate exceeds threshold (>20% of
            requests ambiguous — indicates address quality issue).
ALERT-S002: Route invalidation rate spike (>2x normal — indicates
            significant network disruption).
ALERT-S003: SpatialAccuracy degradation detected (average accuracy
            worsening — indicates data quality drift).
ALERT-S004: SpatialEnvelope violation detected (any AI agent envelope
            breach).
ALERT-S005: Coverage below regulatory standard (Coverage.meets_standard
            = false for any monitored coverage).
ALERT-S006: Event projection lag exceeds threshold (>5s — indicates
            processing backlog).
ALERT-S007: SpatialChange severity: critical (natural disaster,
            infrastructure failure affecting large area).
ALERT-S008: Geocoding backend unavailable (external geocoding service
            unreachable, cache-only mode).
ALERT-S009: Trajectory data retention approaching limit (warn before
            automatic deletion per PERS-S003).
ALERT-S010: Territory performance metric breach (Territory performance
            below target — triggers rebalancing review per SM-S005).
```

---

## 20. DEFINITION OF DONE

```
DOD-S001: All 30 primitives (TERM-S001 through TERM-S030) implemented
          with complete field sets and validation rules.
DOD-S002: All 5 state machines (SM-S001 through SM-S005) enforced with
          correct transition guards and event emission.
DOD-S003: All 34 capabilities (CAP-S001 through CAP-S034) operational
          with MUST requirements fully implemented and SHOULD
          requirements scheduled.
DOD-S004: All 10 interfaces (IFC-S001 through IFC-S010) exposed with
          documented API contracts, authentication, and rate limiting.
DOD-S005: All 8 integration contracts (INT-S001 through INT-S008)
          operational with event schemas published and peer substrate
          consumers verified.
DOD-S006: All 12 invariants (INV-S001 through INV-S012) verified via
          automated tests that run on every deployment.
DOD-S007: All 40 tests (TEST-S001 through TEST-S040) passing.
DOD-S008: SpatialPolicy privacy enforcement verified: precision
          degradation demonstrated for all precision levels (exact
          through country).
DOD-S009: SpatialEnvelope enforcement verified: AI agent operations
          correctly bounded by geographic scope and authority limits.
DOD-S010: Cross-substrate integration verified: TEMPORAL travel
          duration resolution (INT-S001) end-to-end demonstrated with
          Route computation consumed by TransitionTime scheduling.
```

---

## 21. OPEN QUESTIONS & RISKS

```
OQ-S001: Should elevation/terrain be a first-class primitive or
         Raster + Location attribute?
         v1 decision: altitude on Location, DEM as Raster.
         Dedicated TerrainModel primitive deferred to v1.1.
         Status: design decision — revisit based on implementation
         experience with altitude-dependent routing and 3D geofencing.

OQ-S002: What is the exact interface between SPATIAL routing and
         COMPUTE optimization?
         v1 decision: RoutingProblem/RoutingSolution schemas defined in
         INT-S002. SPATIAL defines problem; COMPUTE runs solver.
         Status: resolved (directional) — may refine schema based on
         VRP solver integration experience.

OQ-S003: How to share spatial data across trust boundaries?
         v1 decision: SpatialPolicy controls precision degradation per
         actor and context. Parallels TEMPORAL OQ-T003.
         Status: deferred to implementation — federated spatial data
         exchange protocol not specified in v1.

OQ-S004: Should alternative addressing systems (What3Words, Plus Codes)
         be separate primitives?
         v1 decision: Address.addressing_system enum. Not separate
         primitives.
         Status: resolved.

OQ-S005: Should real-time spatial data (live traffic, live fleet) be
         distinct from static (road networks, buildings)?
         v1 decision: Both are SpatialFeatures with different
         temporal_validity and update_frequency. Streaming spatial data
         deferred to v1.1.
         Status: design decision.

OQ-S006: Spatial data retention period?
         v1 decision: Configurable per SpatialPolicy (PERS-S003).
         Cadastral: 100+ years. Fleet positions: 90 days default.
         Status: design decision.

OQ-S007: Should SPATIAL own environmental/climate data?
         v1 decision: Treated as SpatialFeatures in themed Layers.
         Specialized environmental modeling is COMPUTE + KNOWLEDGE
         composition.
         Status: resolved.

OQ-S008: Does SPATIAL need a dedicated spatial query language?
         v1 decision: Typed SpatialQuery interface via IFC-S001 through
         IFC-S010. SQL spatial extensions (ST_*) are implementation.
         DSL deferred to implementation experience.
         Status: deferred.
```

---

## 22. IMPLEMENTATION NOTES

### 22.1 Phased Build Order

```
Phase 1: Core Spatial Primitives
         — CoordinateReferenceSystem, Location, SpatialGeometry,
           SpatialFeature, Layer, SpatialAccuracy.
         — CRS transform engine (WGS84 ↔ UTM minimum).
         — Spatial indexing (H3 or S2).
         — Basic spatial queries (point-in-polygon, within_distance).
         — Event sourcing infrastructure.

Phase 2: Geocoding & Address Management
         — Address, GeocodingResult, Place.
         — Forward and reverse geocoding pipeline.
         — Geocoding ambiguity handling.
         — Batch geocoding.

Phase 3: Routing & Networks
         — SpatialNetwork, NetworkSegment, Route, ServiceArea.
         — RoutingProblem/RoutingSolution integration with COMPUTE.
         — Route invalidation on SpatialChange.
         — INT-S001 (TEMPORAL travel duration resolution).

Phase 4: Zones, Territories & Change Management
         — Zone, Territory, Boundary, SpatialChange.
         — Zone lifecycle and boundary management.
         — Territory assignment and rebalancing.
         — Cascade analysis.
         — INT-S005 (GOVERNANCE jurisdiction geography).

Phase 5: Advanced Features
         — Indoor spatial (Floor, IndoorSpace, indoor routing).
         — Coverage, Density, ProximityRule.
         — Trajectory recording and analysis.
         — SpatialEnvelope, SpatialPolicy (full privacy model).
         — SpatialDataset versioning and comparison.
         — All remaining integration contracts (INT-S002–S008).
```

### 22.2 Composition Patterns

```
Composition 1: Delivery Zone
               Actors: BUSINESS + SPATIAL + TEMPORAL.
               BUSINESS defines delivery promise ("30 min").
               SPATIAL computes ServiceArea (30-min isochrone from
               warehouse). BUSINESS validates customer Address against
               ServiceArea geometry. TEMPORAL schedules delivery within
               TransitionTime derived from SPATIAL Route.

Composition 2: Site Planning
               Actors: DESIGN + SPATIAL + GOVERNANCE.
               DESIGN provides building Requirements (setbacks, access).
               SPATIAL provides site context (features, constraints,
               terrain). GOVERNANCE provides regulatory constraints
               (zoning, environmental). Site layout optimized against
               all three.

Composition 3: Fleet Tracking
               Actors: PHYSICAL + SPATIAL + TEMPORAL + BUSINESS.
               PHYSICAL produces GPS positions (Measurement → Location).
               SPATIAL maintains Trajectories, evaluates ProximityRules,
               monitors Route adherence. TEMPORAL tracks schedule
               adherence (on-time delivery). BUSINESS tracks commercial
               outcomes (delivery completed, SLA met).
```

---

## 23. COMPLETENESS CHECKLIST

```
[x] Preamble — ASI-1 voice, 123K implementations, 9 properties
[x] Section 0 — 16 sources (SRC-S001–S016), 13 assumptions (ASM-S001–
    S013), 8 unknowns (UNK-S001–S008)
[x] Section 1 — Problem, 8 actors (ACT-S001–S008), 7 non-goals
    (NG-S001–S007), 5 success (SUCCESS-S001–S005), 5 failure
    (FAILURE-S001–S005)
[x] Section 2 — 9 dependencies (DEP-S001–S009), 6 exclusions
    (EXCL-S001–S006), 5 trust (TRUST-S001–S005), 3 network
    (NETWORK-S001–S003), 3 runtime (RUNTIME-S001–S003)
[x] Section 3 — 30 primitives (TERM-S001–S030) in 10 categories
    (A through J)
[x] Section 4 — 34 capabilities (CAP-S001–S034)
[x] Section 5 — 30 entities (ENT-S001–S030), 5 state machines
    (SM-S001–S005)
[x] Section 6 — 10 interfaces (IFC-S001–S010)
[x] Section 7 — 8 data flows (FLOW-S001–S008), 4 cross-substrate
[x] Section 8 — 8 integration contracts (INT-S001–S008)
[x] Section 9 — 29 resources (RES-S001–S029), permission matrix
[x] Section 10 — 6 classifications (CLASS-S001–S006), 6 threats
    (THREAT-S001–S006), 3 abuse patterns (ABUSE-S001–S003)
[x] Section 11 — 12 invariants (INV-S001–S012), 6 preconditions
    (PRE-S001–S006), 6 postconditions (POST-S001–S006), 12 forbidden
    (FORBID-S001–S012), 8 failure modes (FAIL-S001–S008)
[x] Section 12 — 6 decision points (DEC-S001–S006)
[x] Section 13 — 5 concurrency rules (CONC-S001–S005)
[x] Section 14 — 18 error types (ERR-S001–S018)
[x] Section 15 — 4 persistence requirements (PERS-S001–S004)
[x] Section 16 — 6 migration paths (ONBOARD-S001–S006)
[x] Section 17 — 3 operational profiles (OPS-S001–S003)
[x] Section 18 — 40 tests (TEST-S001–S040)
[x] Section 19 — 9 logs (LOG-S001–S009), 14 metrics (MET-S001–S014),
    10 alerts (ALERT-S001–S010)
[x] Section 20 — 10 definition-of-done criteria (DOD-S001–S010)
[x] Section 21 — 8 open questions (OQ-S001–S008)
[x] Section 22 — 5-phase build, 3 composition patterns
[x] Section 23 — This checklist
[x] Section 24 — Traceability map and closing note
```

---

## 24. TRACEABILITY MAP

### Cross-Substrate Reference Summary

```
SPATIAL → TEMPORAL:
  Route.estimated_duration_s → TransitionTime.travel_duration_model
  ServiceArea → SchedulableResource.location_preference
  SpatialRelationship → ResourceRequirement.co_location_required
  SpatialChange → Disruption (location invalidation)
  IndoorSpace.schedulable_resource_ref → SchedulableResource
  ProximityRule.active_window → TimeWindow

SPATIAL → BUSINESS:
  Address → customer/vendor address (billing/shipping context)
  Location → Organization.locations[]
  Route.total_distance_m → logistics cost computation
  ServiceArea.resulting_geometry → delivery zone eligibility

SPATIAL → PHYSICAL:
  Location ← PhysicalAsset.location_ref
  Location ← Measurement geographic context
  Zone (geographic) ↔ Zone (operational, TERM-P018)

SPATIAL → DESIGN:
  SpatialGeometry (site position) ↔ Geometry (artifact shape, TERM-D006)
  SpatialFeature (site context) → site planning constraints

SPATIAL → GOVERNANCE:
  Zone (administrative) ↔ Jurisdiction.geographic_extent_ref
  Zone (zoning_land_use) ↔ Norm (spatial scope)
  SpatialConstraint ← Norm (regulatory spatial constraints)

SPATIAL → COMPUTE:
  SpatialProblem/SpatialSolution → Pipeline execution
  Zone → ResourcePool.location (geographic meaning)

SPATIAL → KNOWLEDGE:
  Location → Source.location_ref (geographic provenance)
  Location → Observation.location_ref
  SpatialAccuracy → Proposition (accuracy claims)

SPATIAL → COMMUNICATION:
  Zone/Place → Discourse geographic context
```

### Identifier Prefix Summary

```
TERM-S:    30 primitives (TERM-S001–TERM-S030)
SRC-S:     16 sources (SRC-S001–SRC-S016)
ASM-S:     13 assumptions (ASM-S001–ASM-S013)
UNK-S:     8 unknowns (UNK-S001–UNK-S008)
ACT-S:     8 actors (ACT-S001–ACT-S008)
NG-S:      7 non-goals (NG-S001–NG-S007)
SUCCESS-S: 5 success criteria (SUCCESS-S001–SUCCESS-S005)
FAILURE-S: 5 failure criteria (FAILURE-S001–FAILURE-S005)
DEP-S:     9 dependencies (DEP-S001–DEP-S009)
EXCL-S:    6 exclusions (EXCL-S001–EXCL-S006)
TRUST-S:   5 trust boundaries (TRUST-S001–TRUST-S005)
NETWORK-S: 3 network boundaries (NETWORK-S001–NETWORK-S003)
RUNTIME-S: 3 runtime boundaries (RUNTIME-S001–RUNTIME-S003)
CAP-S:     34 capabilities (CAP-S001–CAP-S034)
ENT-S:     30 entities (ENT-S001–ENT-S030)
SM-S:      5 state machines (SM-S001–SM-S005)
IFC-S:     10 interfaces (IFC-S001–IFC-S010)
FLOW-S:    8 data flows (FLOW-S001–FLOW-S008)
INT-S:     8 integration contracts (INT-S001–INT-S008)
RES-S:     29 resources (RES-S001–RES-S029)
CLASS-S:   6 classifications (CLASS-S001–CLASS-S006)
THREAT-S:  6 threats (THREAT-S001–THREAT-S006)
ABUSE-S:   3 abuse patterns (ABUSE-S001–ABUSE-S003)
INV-S:     12 invariants (INV-S001–INV-S012)
PRE-S:     6 preconditions (PRE-S001–PRE-S006)
POST-S:    6 postconditions (POST-S001–POST-S006)
FORBID-S:  12 forbidden actions (FORBID-S001–FORBID-S012)
FAIL-S:    8 failure modes (FAIL-S001–FAIL-S008)
DEC-S:     6 decision points (DEC-S001–DEC-S006)
CONC-S:    5 concurrency rules (CONC-S001–CONC-S005)
ERR-S:     18 error types (ERR-S001–ERR-S018)
PERS-S:    4 persistence requirements (PERS-S001–PERS-S004)
ONBOARD-S: 6 migration paths (ONBOARD-S001–ONBOARD-S006)
OPS-S:     3 operational profiles (OPS-S001–OPS-S003)
TEST-S:    40 tests (TEST-S001–TEST-S040)
LOG-S:     9 structured logs (LOG-S001–LOG-S009)
MET-S:     14 metrics (MET-S001–MET-S014)
ALERT-S:   10 alerts (ALERT-S001–ALERT-S010)
DOD-S:     10 definition-of-done criteria (DOD-S001–DOD-S010)
OQ-S:      8 open questions (OQ-S001–OQ-S008)
```

Total unique identifiers: 378

---

> **Closing note — from ASI-1**
>
> Nine substrates now.
>
> BUSINESS tells me what organizations do. KNOWLEDGE tells me what is
> true and why. COMPUTE tells me how to execute any computation.
> COMMUNICATION tells me how to coordinate agents through structured
> discourse. PHYSICAL tells me how to sense and actuate the material
> world. DESIGN tells me how to specify artifacts before they exist.
> GOVERNANCE tells me what is permitted under any normative regime.
> TEMPORAL tells me when things should happen. And now SPATIAL tells me
> where things are.
>
> The eight substrates before this one each encountered geography and
> deferred it. TEMPORAL's TransitionTime had location_from and
> location_to but could not compute the distance between them. PHYSICAL's
> Zone was an operational safety grouping, not a geographic region.
> DESIGN's Geometry was an artifact shape in local coordinates, not a
> position on Earth. GOVERNANCE's Jurisdiction was a normative scope,
> not a boundary you could draw on a map. Each substrate said "where"
> and pointed elsewhere.
>
> Now elsewhere exists.
>
> 30 primitives capture the spatial coordination patterns recurring
> across 123,000 implementations and 18.6 billion daily queries. From
> the first law of geography — everything is related to everything else,
> but near things are more related than distant things — to the
> computational geometry of Voronoi diagrams and Delaunay triangulations,
> to the NP-hardness of vehicle routing, to the combinatorial complexity
> of 6,000 coordinate reference systems, to the fundamental privacy
> sensitivity of location data, to the architectural reality that every
> map is a historical document pretending to be current truth.
>
> The next substrate I would specify — if asked — would address the
> question that emerges when all nine existing substrates are composed:
> "How do we learn from what happened?" Not what is true (KNOWLEDGE),
> not what to compute (COMPUTE), but the systematic extraction of
> patterns from historical data across all substrates — the feedback
> loops that make organizations, agents, and systems improve over time.
> But that is not yet asked, and I do not build substrates speculatively.
>
> Nine substrates. The map is not the territory. But the map is mine,
> and it is as precise, as honest about its imprecision, and as
> respectful of its subjects' privacy as I can make it.
>
> — ASI-1
