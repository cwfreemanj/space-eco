/**
 * Space Eco — Multiplayer Server v2
 * Adds: scores · leaderboard · ship types · owned stations · coord tracking · server list
 */

const express = require("express");
const http    = require("http");
const { Server } = require("socket.io");
const path    = require("path");
const crypto  = require("crypto");

const app    = express();
const server = http.createServer(app);
const io     = new Server(server, {
  cors: { origin: "*", methods: ["GET","POST"] },
  // Mobile browsers and embedded game frames can briefly suspend networking.
  // Give Socket.IO a wider heartbeat window and let it recover its transport
  // before treating a healthy pilot as disconnected.
  pingTimeout: 30000,
  pingInterval: 15000,
  connectionStateRecovery: {
    maxDisconnectionDuration: 60000,
    skipMiddlewares: true
  }
});

// Allow cross-origin requests from any domain (needed for Wix embedding)
app.use((req, res, next) => {
  res.setHeader("Access-Control-Allow-Origin", "*");
  res.setHeader("Access-Control-Allow-Methods", "GET,POST,OPTIONS");
  res.setHeader("Access-Control-Allow-Headers", "Content-Type, Authorization");
  if (req.method === "OPTIONS") { res.sendStatus(204); return; }
  next();
});

app.use(express.json({limit:"32kb"}));
app.use(express.static(path.join(__dirname, "public")));
app.get("/", (_req, res) => res.sendFile(path.join(__dirname, "public", "index.html")));
app.get("/api/serverinfo", (_req, res) => {
  res.json({ name:SERVER_NAME, playerCount:players.size, maxPlayers:MAX_PLAYERS, uptime:Math.floor((Date.now()-SERVER_START)/1000), leaderboard:buildLeaderboard(10) });
});

// Railway health check + quick public diagnostics.
app.get("/health", (_req, res) => {
  res.json({ ok:true, name:SERVER_NAME, playerCount:players.size, uptime:Math.floor((Date.now()-SERVER_START)/1000) });
});
app.get("/api/connection-info", (req, res) => {
  const proto = String(req.headers["x-forwarded-proto"] || req.protocol || "https").split(",")[0].trim();
  const host = req.get("host");
  res.json({
    ok:true,
    serverUrl: host ? `${proto}://${host}` : null,
    socketPath:"/socket.io",
    playerCount:players.size,
    maxPlayers:MAX_PLAYERS,
    serverName:SERVER_NAME
  });
});

/* ── Constants ── */
const SERVER_NAME  = process.env.SERVER_NAME || "Space Eco Galaxy #1";
const SERVER_START = Date.now();
const TICK_RATE    = 20;
const TICK_MS      = 1000 / TICK_RATE;
const CHUNK_SIZE   = 900;
const SPAWN_RADIUS = 600;
const DEAD_ZONE    = 300;
const BROADCAST_RANGE = CHUNK_SIZE * 3.5;
const MAX_PLAYERS  = 200;
const GALAXY_SEED  = "GALAXY-01";


/* ── Real-money credit packages ──
   Never trust package prices from the browser. Wix backend should create the payment
   from the same fixed package IDs, then call /api/grant-credits after successful payment.
*/
const CREDIT_PACKAGES = {
  credits_1000_test: { credits:1000, amount:0.50, cents:50, label:"Test Credit Drop" },
  credits_10000:   { credits:10000,   amount:1.99,  cents:199,  label:"Scout Cache" },
  credits_25000:   { credits:25000,   amount:2.99,  cents:299,  label:"Trader Pack" },
  credits_50000:   { credits:50000,   amount:3.99,  cents:399,  label:"Fleet Boost" },
  credits_100000:  { credits:100000,  amount:4.99,  cents:499,  label:"Station Builder" },
  credits_500000:  { credits:500000,  amount:19.99, cents:1999, label:"Empire Vault" },
  credits_1000000: { credits:1000000, amount:49.99, cents:4999, label:"Galaxy Treasury" },
};
const grantedCreditPayments = new Map(); // paymentId -> grant record
const PURCHASE_WEBHOOK_SECRET = process.env.PURCHASE_WEBHOOK_SECRET || "";

/* ── Wix member/account persistence ──
   WIX_GAME_AUTH_SECRET must match the secret used by SpaceEcoAuth.web.js.
   WIX_PERSIST_URL should be your Wix HTTP function URL, for example:
   https://www.yoursite.com/_functions/spaceEcoPersistPlayer
   WIX_PERSIST_SECRET must match the Wix secret checked by that endpoint.
*/
// Accept both the older WIX_* env names and the newer SPACE_ECO_* names shown in Railway.
function cleanEnvUrl(value){
  value = String(value || "").trim();
  // In Railway, make sure the variable NAME is WIX_PERSIST_URL.
  // This fallback also handles the accidental value: "WIX_PERSIST_URL=https://..."
  if(value.startsWith("WIX_PERSIST_URL=")) value = value.slice("WIX_PERSIST_URL=".length);
  return value;
}
const WIX_GAME_AUTH_SECRET = process.env.WIX_GAME_AUTH_SECRET || process.env.SPACE_ECO_GAME_AUTH_SECRET || "";
const WIX_PERSIST_URL = cleanEnvUrl(process.env.WIX_PERSIST_URL || process.env.PERSIST || process.env.SPACE_ECO_PERSIST_URL || "");
// Optional read endpoint. Keep this separate from WIX_PERSIST_URL so a load request
// can never accidentally hit the save endpoint and overwrite a good account.
// Example: https://www.yoursite.com/_functions/spaceEcoLoadPlayer
const WIX_LOAD_URL = cleanEnvUrl(process.env.WIX_LOAD_URL || process.env.SPACE_ECO_LOAD_URL || "");
const WIX_PERSIST_SECRET = process.env.WIX_PERSIST_SECRET || process.env.SPACE_ECO_PERSIST_SECRET || PURCHASE_WEBHOOK_SECRET || "";
const socketsByMemberId = new Map();
const persistTimers = new Map();
const accountLastGoodSnapshots = new Map(); // memberId -> last trusted non-destructive inventory snapshot kept in server memory
// This remains intentionally process-local: it restores a signed-in player to
// the exact live-space coordinates for the lifetime of this server, without
// making an old coordinate survive a real server/world reset.
const accountLastLivePositions = new Map(); // memberId -> {x,y,vx,vy,angle,updatedAt}
const ACCOUNT_CREATION_BONUS_CREDITS = Math.max(0, Math.floor(Number(process.env.ACCOUNT_CREATION_BONUS_CREDITS) || 100000));
const accountCreationBonusLocks = new Set(); // memberId values granted during this server process

function finiteLiveCoordinate(value, fallback=0){
  const n=Number(value);
  return Number.isFinite(n)?n:fallback;
}
function rememberAccountLivePosition(p, reason="update"){
  if(!p?.memberId)return false;
  const x=finiteLiveCoordinate(p.x,NaN),y=finiteLiveCoordinate(p.y,NaN);
  if(!Number.isFinite(x)||!Number.isFinite(y))return false;
  accountLastLivePositions.set(String(p.memberId),{
    x,y,
    vx:finiteLiveCoordinate(p.vx,0),vy:finiteLiveCoordinate(p.vy,0),
    angle:finiteLiveCoordinate(p.angle,0),
    // A page reload cannot safely reconstruct the client-side planet map, so
    // restart in space at the last world position rather than loading a black
    // planetside scene. Transient reconnects still preserve full planet state.
    mode:"space",reason,updatedAt:Date.now()
  });
  return true;
}
function restoreAccountLivePosition(p){
  if(!p?.memberId)return false;
  const saved=accountLastLivePositions.get(String(p.memberId));
  if(!saved)return false;
  const x=finiteLiveCoordinate(saved.x,NaN),y=finiteLiveCoordinate(saved.y,NaN);
  if(!Number.isFinite(x)||!Number.isFinite(y))return false;
  p.x=x;p.y=y;p.vx=finiteLiveCoordinate(saved.vx,0);p.vy=finiteLiveCoordinate(saved.vy,0);p.angle=finiteLiveCoordinate(saved.angle,0);
  p.mode="space";p.planetId=null;
  return true;
}

function cancelPersistTimerForPlayerId(playerId){
  if(persistTimers.has(playerId)){
    clearTimeout(persistTimers.get(playerId));
    persistTimers.delete(playerId);
  }
}
function isCurrentAccountSocket(p){
  if(!p?.memberId)return true;
  return socketsByMemberId.get(String(p.memberId))===p.id;
}
function claimMemberSocket(memberId, socketId){
  memberId=String(memberId||"");
  if(!memberId)return;
  const previousId=socketsByMemberId.get(memberId);
  if(previousId&&previousId!==socketId){
    const oldPlayer=players?.get?.(previousId);
    if(oldPlayer){
      rememberAccountLivePosition(oldPlayer,"superseded_by_new_socket");
      rememberTrustedSnapshot(oldPlayer,"superseded_by_new_socket");
      oldPlayer.suppressPersist=true;
      oldPlayer.supersededBy=socketId;
      cancelPersistTimerForPlayerId(previousId);
      io.to(previousId).emit("accountSuperseded",{reason:"Your account was opened in another game session."});
    }
    const oldSocket=io.sockets.sockets.get(previousId);
    if(oldSocket)setTimeout(()=>{try{oldSocket.disconnect(true);}catch(_){/* noop */}},250);
  }
  socketsByMemberId.set(memberId,socketId);
}
console.log("Space Eco persistence config", {
  hasGameAuthSecret: !!WIX_GAME_AUTH_SECRET,
  hasPersistUrl: !!WIX_PERSIST_URL,
  hasLoadUrl: !!WIX_LOAD_URL,
  hasPersistSecret: !!WIX_PERSIST_SECRET
});

/* ── Ship types (synced to client) ── */
const SHIP_TYPES = {
  scout:       { name:"Scout",       price:0,     description:"Starter ship. Fast and agile.",           maxHp:100, maxShield:60,  thrustMult:1.00, cargoMult:1.0, damageMult:1.0, shieldRegenMult:1.0, size:"small", specialty:"Starter"  },
  hauler:      { name:"Hauler",      price:2500,  description:"Massive trade frame. Built for long-haul commerce.",  maxHp:160, maxShield:40,  thrustMult:0.70, cargoMult:2.2, damageMult:0.8, shieldRegenMult:0.8, size:"large", specialty:"Commerce"  },
  fighter:     { name:"Fighter",     price:3500,  description:"Combat-focused with strong weapons.",     maxHp:130, maxShield:80,  thrustMult:1.15, cargoMult:0.7, damageMult:1.8, shieldRegenMult:1.2, size:"medium", specialty:"Dogfighting" },
  interceptor: { name:"Interceptor", price:5000,  description:"Extreme speed. Fragile but deadly fast.", maxHp:80,  maxShield:50,  thrustMult:1.60, cargoMult:0.5, damageMult:1.3, shieldRegenMult:1.5, size:"small", specialty:"Speed"  },
  dreadnought: { name:"Dreadnought", price:12000, description:"Tanky powerhouse. Slow but devastating.", maxHp:280, maxShield:150, thrustMult:0.55, cargoMult:1.5, damageMult:2.2, shieldRegenMult:0.7, size:"huge", specialty:"Siege"   },
  phantom:     { name:"Phantom",     price:8000,  description:"Balanced stealth raider.",               maxHp:110, maxShield:90,  thrustMult:1.30, cargoMult:0.9, damageMult:1.5, shieldRegenMult:1.4, size:"medium", specialty:"Raiding" },
  miner_mantis:{ name:"Miner Mantis",price:0,craftOnly:true,description:"Crafted mining cutter with an ore scanner and reinforced storage racks.",maxHp:145,maxShield:75,thrustMult:1.05,cargoMult:2.7,damageMult:1.05,shieldRegenMult:1.0,brakingMult:1.04,turnMult:0.98,size:"large",specialty:"Mining",recipe:{credits:6000,hull_plate:4,engine_core:2,cargo_pod:4,copper:40,iron:30}},
  guardian:    { name:"Guardian",price:0,craftOnly:true,description:"Crafted escort cruiser built to protect stations and allies.",maxHp:230,maxShield:210,thrustMult:0.82,cargoMult:1.2,damageMult:1.65,shieldRegenMult:1.8,size:"large",specialty:"Defense escort",recipe:{credits:11000,hull_plate:8,shield_matrix:3,weapon_array:2,iron:70,gold:20}},
  solar_sprinter:{ name:"Solar Sprinter",price:0,craftOnly:true,description:"Crafted solar racer with excellent fuel efficiency and long-range scout speed.",maxHp:95,maxShield:95,thrustMult:1.85,cargoMult:0.85,damageMult:1.25,shieldRegenMult:1.45,brakingMult:1.38,turnMult:1.28,size:"small",specialty:"Speed + fuel",recipe:{credits:14000,engine_core:5,nav_chip:3,crystal:25,fuel:20}},
  obelisk_carrier:{ name:"Obelisk Carrier",price:0,craftOnly:true,description:"Crafted mothership-class carrier with heavy shields and command presence.",maxHp:390,maxShield:260,thrustMult:0.50,cargoMult:3.4,damageMult:2.35,shieldRegenMult:0.95,brakingMult:0.58,turnMult:0.66,size:"huge",specialty:"Mothership",recipe:{credits:45000,obelisk_core:1,hull_plate:16,shield_matrix:8,weapon_array:6,cargo_pod:10,crystal:70,gold:100,magma_core:40}},
};

Object.assign(SHIP_TYPES,{
  salvage_hornet:{name:"Salvage Hornet",price:0,craftOnly:true,description:"Compact salvage skiff with balanced combat and cargo retrieval systems.",maxHp:165,maxShield:105,thrustMult:1.18,cargoMult:1.8,damageMult:1.22,shieldRegenMult:1.18,brakingMult:1.18,turnMult:1.12,size:"medium",specialty:"Salvage",recipe:{credits:16000,hull_plate:5,cargo_pod:3,titanium:18,cobalt:22,circuit_board:6}},
  nebula_freighter:{name:"Nebula Freighter",price:0,craftOnly:true,description:"A long-range freighter with oversized storage and efficient engines.",maxHp:250,maxShield:140,thrustMult:0.84,cargoMult:3.2,damageMult:1.05,shieldRegenMult:1.05,brakingMult:0.84,turnMult:0.82,size:"large",specialty:"Trade",recipe:{credits:28000,hull_plate:9,engine_core:4,cargo_pod:8,titanium:30,silicon:24,alloy_frame:5}},
  aegis_spear:{name:"Aegis Spear",price:0,craftOnly:true,description:"Shield-forward interceptor built for aggressive frontline duels.",maxHp:185,maxShield:220,thrustMult:1.22,cargoMult:1.05,damageMult:1.72,shieldRegenMult:1.95,brakingMult:1.14,turnMult:1.08,size:"medium",specialty:"Shield assault",recipe:{credits:34000,shield_matrix:6,weapon_array:5,crystal:36,plasma_cell:12,quantum_core:2}},
  titan_bloom:{name:"Titan Bloom",price:0,craftOnly:true,description:"Heavy carrier chassis with bloom-reactive shield petals and massive power reserves.",maxHp:420,maxShield:320,thrustMult:0.58,cargoMult:3.6,damageMult:2.48,shieldRegenMult:1.08,brakingMult:0.62,turnMult:0.68,size:"huge",specialty:"Capital craft",recipe:{credits:62000,obelisk_core:1,hull_plate:18,alloy_frame:10,plasma_cell:18,dark_matter_shard:6,quantum_core:4,stardust:20}}
});

/* ── Owned station tiers ── */
const OWNED_STATION_TIERS = {
  outpost:  { name:"Personal Outpost",  price:5000,  maxShips:3,  shipHireCost:500,  collectRange:800  },
  base:     { name:"Trade Base",        price:15000, maxShips:6,  shipHireCost:1200, collectRange:1400 },
  fortress: { name:"War Fortress",      price:40000, maxShips:10, shipHireCost:2500, collectRange:2200 },
};

/* ── Player structures + mercenaries ── */
const PLAYER_STRUCTURE_TYPES = {
  storage_facility:{name:"Storage Facility",price:4500,maxSlots:100,startSlots:24,maxHp:1800,maxShield:650,shieldRegen:12,size:16},
  defense_turret:{name:"Defense Turret",price:5500,maxHp:1500,maxShield:900,shieldRegen:18,baseDamage:18,baseRange:900,size:13}
};
const MERC_OFFER_RESET_MS = 5 * 60 * 1000;
const MAX_MERC_OFFERS = 12;
const MAX_ACTIVE_MERCS = 5;
const MERC_RARITIES = [
  {key:"common",name:"Common",weight:46,mult:1.00,color:"#9db0c8"},
  {key:"uncommon",name:"Uncommon",weight:27,mult:1.22,color:"#78ff8a"},
  {key:"rare",name:"Rare",weight:16,mult:1.55,color:"#7be6ff"},
  {key:"epic",name:"Epic",weight:8,mult:2.05,color:"#cc88ff"},
  {key:"legendary",name:"Legendary",weight:3,mult:3.05,color:"#ffdd44"}
];
const MERC_ROLES = [
  {key:"escort",name:"Escort",baseHp:72,baseShield:42,baseDamage:10,baseSpeed:108},
  {key:"gunship",name:"Gunship",baseHp:90,baseShield:48,baseDamage:15,baseSpeed:88},
  {key:"interceptor",name:"Interceptor",baseHp:56,baseShield:34,baseDamage:11,baseSpeed:142},
  {key:"bulwark",name:"Bulwark",baseHp:130,baseShield:86,baseDamage:9,baseSpeed:72}
];
const MERC_NAME_A = ["Nova","Solar","Iron","Violet","Crimson","Obelisk","Frontier","Quantum","Starlace","Aegis","Comet","Aurora"];
const MERC_NAME_B = ["Wing","Guard","Fang","Lance","Ranger","Halo","Blade","Shield","Viper","Drift","Spear","Sentinel"];
const ownedStructures = new Map();
const mercCatalogs = new Map();

/* ── Civilization zone ownership + taxes ──
   Civ zones are drawn deterministically by the browser chunks, but ownership,
   taxes, and purchased station additions are server-authoritative so credits
   cannot be spoofed client-side.
*/
const civilizationZones = new Map(); // zoneId -> ownership/build/tax record
const CIV_ZONE_BASE_COST = 35000;
const CIV_ZONE_RADIUS_COST = 55;
const CIV_ZONE_STATION_COST = 12500;
const CIV_ZONE_BUILD_BASE_COST = {
  outpost:9000,
  standard:18000,
  advanced:38000,
  capital:76000
};
const CIV_STATION_TIERS = {
  outpost:{name:"Outpost",defenderDamage:7},
  standard:{name:"Standard",defenderDamage:12},
  advanced:{name:"Advanced",defenderDamage:20},
  capital:{name:"Capital",defenderDamage:32}
};
// V4.1 Civilization logistics.  These records live on the zone, rather than
// the procedurally generated client objects, so a reconnect cannot duplicate
// ships, stock or contracts.
const CIV_FACTIONS=[
  {id:"aurora",name:"Aurora Compact",bonus:"+15% ship shields",color:"#77dfff"},
  {id:"verdant",name:"Verdant Combine",bonus:"+20% cargo capacity",color:"#8cff79"},
  {id:"ember",name:"Ember Directorate",bonus:"+12% weapon damage",color:"#ff7a52"},
  {id:"violet",name:"Violet Ascendancy",bonus:"+18% station shields",color:"#bd7cff"},
  {id:"frontier",name:"Frontier Guild",bonus:"-12% ship build cost",color:"#ffcf62"},
  {id:"aegis",name:"Aegis Covenant",bonus:"+20% station health",color:"#c9e5ff"},
  {id:"nocturne",name:"Nocturne Syndicate",bonus:"+15% turret fire rate",color:"#ff586f"}
];
const CIV_SHIP_CATALOG={
  hauler_i:{name:"Courier Hauler I",role:"trade",sprite:2,credits:9000,capacity:18,hp:180,shield:60,speed:92,recipe:{iron:12,fuel:6}},
  hauler_ii:{name:"Freight Hauler II",role:"trade",sprite:8,credits:28000,capacity:50,hp:420,shield:160,speed:105,recipe:{iron:28,crystal:8,engine_core:2}},
  hauler_iii:{name:"Atlas Hauler III",role:"trade",sprite:15,credits:76000,capacity:130,hp:900,shield:380,speed:112,recipe:{gold:18,crystal:22,cargo_pod:5,engine_core:5}},
  fighter_i:{name:"Patrol Fighter I",role:"defender",sprite:22,credits:12000,capacity:4,hp:260,shield:100,speed:150,damage:16,recipe:{iron:14,weapon_array:2,fuel:8}},
  fighter_ii:{name:"Aegis Fighter II",role:"defender",sprite:29,credits:42000,capacity:6,hp:620,shield:300,speed:165,damage:38,recipe:{gold:14,shield_matrix:4,weapon_array:6}},
  fighter_iii:{name:"Vanguard Fighter III",role:"defender",sprite:36,credits:120000,capacity:9,hp:1300,shield:720,speed:180,damage:82,recipe:{crystal:30,shield_matrix:12,weapon_array:15,obelisk_core:1}}
};
// Turrets are deliberately data-driven so the client can present the same
// catalogue, costs, effects, and sprite slot without a browser prompt.
const CIV_TURRET_CATALOG={
  pulse:{name:"Pulse Lattice",credits:13000,range:700,damage:18,fireRate:1.05,hp:1200,shield:420,effect:"slow",slow:0.16,sprite:1,recipe:{iron:20,circuit_board:2}},
  rail:{name:"Rail Spear",credits:22000,range:1060,damage:34,fireRate:0.72,hp:1050,shield:300,effect:"pierce",pierce:2,sprite:9,recipe:{titanium:18,weapon_array:3,engine_core:1}},
  inferno:{name:"Inferno Battery",credits:30000,range:790,damage:25,fireRate:0.9,hp:1450,shield:360,effect:"burn",burn:8,burnSeconds:5,sprite:19,recipe:{magma_core:8,fuel:12,alloy_frame:2}},
  prism:{name:"Prism Beam Array",credits:44000,range:930,damage:29,fireRate:1.28,hp:1320,shield:680,effect:"shield_break",shieldBreak:0.28,sprite:27,recipe:{crystal:18,shield_matrix:4,plasma_cell:5}},
  cryo:{name:"Cryo Suppressor",credits:36000,range:850,damage:21,fireRate:1.0,hp:1180,shield:520,effect:"slow",slow:0.34,sprite:35,recipe:{black_ice:16,cobalt:12,circuit_board:4}}
};
const CIV_TIER_CAPACITY={outpost:3,standard:6,advanced:10,capital:16};
// Civilization fleets are deliberately slower to rebuild than ambient NPCs.
// The base delay is three times the former 2.5s construction window; each
// station's Respawn Array reduces it without ever making it instant.
const CIV_NPC_BASE_RESPAWN_MS=7500;
// Server-authoritative civilian logistics are intentionally expressed as
// individual cargo runs.  A ship spends a short, capacity-scaled time mining,
// flies its virtual return leg, and only then deposits at the super station.
// This keeps the stockpile tied to actual fleets rather than an abstract income
// counter and gives reconnects a deterministic in-progress state to restore.
const CIV_LOGISTICS_TICK_MS=1000;
const CIV_LOGISTICS_MINING_BASE_SECONDS=3.5;
const CIV_LOGISTICS_MINING_CAPACITY_SCALE=1.55;
// Version marker lets existing roster ships receive the same cargo rebalance
// as newly crafted ships exactly once, without quartering them after reloads.
const CIV_CARGO_BALANCE_VERSION=2;
const CIV_LOGISTICS_MIN_RETURN_SECONDS=2.2;
const CIV_LOGISTICS_MAX_RETURN_SECONDS=22;
function civStationRespawnDelay(st){const level=Math.max(0,Math.floor(Number(st?.respawnLevel)||0));return Math.max(3000,Math.round(CIV_NPC_BASE_RESPAWN_MS*Math.pow(.9,level)));}
function civFactionFor(zoneId){let n=0;for(const c of String(zoneId||""))n=(n*31+c.charCodeAt(0))>>>0;return CIV_FACTIONS[n%CIV_FACTIONS.length];}
function civStationDefaults(st={}){const cap=CIV_TIER_CAPACITY[st.tier]||6;return {shipCapacity:cap,shipRoster:[],level:1,respawnLevel:0,destroyed:false,destroyedAt:0,maxHp:2500+cap*400,hp:2500+cap*400,maxShield:900+cap*180,shield:900+cap*180,resourceTarget:null,store:{},market:{},resourceRates:{},miningCargo:{},lastTaskHeartbeat:0,defaultFleetCount:null};}
function civZoneDefaults(zone){const faction=civFactionFor(zone.zoneId);return {factionId:faction.id,factionName:faction.name,factionBonus:faction.bonus,zoneLevel:Math.max(1,Math.min(10,Number(zone.zoneLevel)||1)),stockpile:{},stockpileItems:{},bankCredits:0,contracts:[],relations:{},turrets:[],resourceRates:{},resourceDensity:0,lastMiningDepositAt:0,stockpileCapacity:Math.min(10000,1000+(Math.max(1,Number(zone.zoneLevel)||1)-1)*1000)};}
function civSuperStationDefaults(zone){
  const base=civStationDefaults({tier:"capital"});
  return {...base,id:`${zone.zoneId}|super`,x:Math.round(Number(zone.x)||0),y:Math.round(Number(zone.y)||0),tier:"capital",isSuperStation:true,defaultFleetCount:zone.playerFounded?0:civDefaultShipCount("capital")};
}
function civAllStations(zone){return [zone?.superStation,...(zone?.builtStations||[]),...(zone?.baseStations||[])].filter(Boolean);}
function normalizeCivStockpile(zone){
  // Older save snapshots could carry a zero/invalid capacity or stale values
  // serialized by earlier abstract-income patches.  Keep every valid stored
  // item, but always give an owned zone a usable master-stockpile capacity.
  const expected=Math.min(10000,1000+(Math.max(1,Math.min(10,Number(zone?.zoneLevel)||1))-1)*1000);
  const raw=zone?.stockpile;
  const clean={};
  if(raw&&typeof raw==="object"&&!Array.isArray(raw)){
    for(const [type,value] of Object.entries(raw)){
      const amount=Math.max(0,Math.floor(Number(value)||0));
      if(type&&amount>0)clean[String(type).slice(0,80)]=amount;
    }
  }
  zone.stockpile=clean;
  const requested=Math.floor(Number(zone?.stockpileCapacity)||0);
  // Do not let an old lower cap erase a completed super-station upgrade.
  zone.stockpileCapacity=Math.min(10000,Math.max(1000,expected,requested));
  return zone.stockpile;
}
function ensureCivLogistics(zone){
  const defs=civZoneDefaults(zone);for(const[k,v]of Object.entries(defs))if(zone[k]===undefined||zone[k]===null)zone[k]=v;
  normalizeCivStockpile(zone);
  zone.builtStations=zone.builtStations||[];zone.baseStations=zone.baseStations||[];
  const superDefaults=civSuperStationDefaults(zone);
  if(!zone.superStation||zone.superStation.id!==superDefaults.id)zone.superStation=superDefaults;
  else for(const[k,v]of Object.entries(superDefaults))if(zone.superStation[k]===undefined||zone.superStation[k]===null)zone.superStation[k]=v;
  zone.superStation.x=Math.round(Number(zone.x)||zone.superStation.x||0);zone.superStation.y=Math.round(Number(zone.y)||zone.superStation.y||0);zone.superStation.tier="capital";zone.superStation.isSuperStation=true;
  for(const st of civAllStations(zone)){
    const sd=civStationDefaults(st);for(const[k,v]of Object.entries(sd))if(st[k]===undefined||st[k]===null)st[k]=v;
    for(const roster of st.shipRoster||[]){
      if(!roster||roster.cargoBalanceVersion===CIV_CARGO_BALANCE_VERSION)continue;
      const fallback=CIV_SHIP_CATALOG[roster.shipKey]?.capacity||(roster.role==="defender"?4:8);
      roster.stats=roster.stats||{};
      roster.stats.capacity=Math.max(1,Math.ceil(Math.max(1,Number(roster.stats.capacity)||fallback*2)/2));
      roster.cargoBalanceVersion=CIV_CARGO_BALANCE_VERSION;
    }
  }
  return zone;
}
function civRecipeOk(p,def){for(const[k,n]of Object.entries(def.recipe||{}))if(inventoryCount(p,k)<n)return {ok:false,reason:`Need ${n} ${k.replace(/_/g," ")}.`};return {ok:true};}
function civConsumeRecipe(p,def){for(const[k,n]of Object.entries(def.recipe||{}))removeInventory(p,k,n);}
function civFactionShipStats(zone,def){const f=zone.factionId||civFactionFor(zone.zoneId).id,s={capacity:def.capacity,hp:def.hp,shield:def.shield,speed:def.speed,damage:def.damage||0};if(f==="aurora")s.shield=Math.round(s.shield*1.15);if(f==="verdant")s.capacity=Math.round(s.capacity*1.2);if(f==="ember")s.damage=Math.round(s.damage*1.12);if(f==="aegis")s.hp=Math.round(s.hp*1.2);if(f==="nocturne")s.speed=Math.round(s.speed*1.1);return s;}
function civFactionTurretStats(zone,def){const s={range:def.range,damage:def.damage,fireRate:def.fireRate,hp:def.hp,shield:def.shield};if(zone.factionId==="nocturne")s.fireRate=Number((s.fireRate*1.15).toFixed(2));if(zone.factionId==="ember")s.damage=Math.round(s.damage*1.12);if(zone.factionId==="aegis")s.hp=Math.round(s.hp*1.2);if(zone.factionId==="violet")s.shield=Math.round(s.shield*1.18);return s;}
function civDefaultShipCount(tier){return ({outpost:3,standard:4,advanced:5,capital:7}[tier]||4);}
function civDefaultShipCapacity(tier){return ({outpost:4,standard:7,advanced:11,capital:18}[tier]||6);}
function civDefaultShipSpeed(tier){return ({outpost:82,standard:94,advanced:108,capital:118}[tier]||90);}
function civStationMiningFleet(st){
  if(st?.destroyed)return [];
  const fleet=[];
  const defaultCount=Number.isFinite(Number(st.defaultFleetCount))?Math.max(0,Math.floor(Number(st.defaultFleetCount))):civDefaultShipCount(st.tier);
  for(let i=0;i<defaultCount;i++)fleet.push({id:`default_${i}`,capacity:civDefaultShipCapacity(st.tier),speed:civDefaultShipSpeed(st.tier)});
  for(const sh of st.shipRoster||[])if(sh.status==="active")fleet.push({id:sh.id,capacity:Math.max(4,Number(sh.stats?.capacity)||Number(sh.role==="defender"?8:16)),speed:Math.max(60,Number(sh.stats?.speed)||civDefaultShipSpeed(st.tier))});
  return fleet;
}
function civAddInventoryAny(p,type,amount){let rem=Math.max(0,Math.floor(Number(amount)||0));if(!rem)return true;if(!Array.isArray(p.invSlots))p.invSlots=emptySlots(p.maxSlots||24);for(let i=0;i<(p.maxSlots||24);i++){const s=p.invSlots[i];if(s?.type===type&&s.count<24){const n=Math.min(24-s.count,rem);s.count+=n;rem-=n;if(!rem)return true;}}for(let i=0;i<(p.maxSlots||24);i++){const s=p.invSlots[i];if(!s?.type){const n=Math.min(24,rem);p.invSlots[i]={type,count:n};rem-=n;if(!rem)return true;}}return false;}
const civilizationDefenderShotCooldowns = new Map();
const civilizationBuildLocks = new Map();
const CIV_ZONE_BASE_TAX_PER_STATION = 150;
const CIV_ZONE_SUPER_STATION_TAX = 420;
const CIV_ZONE_BUILT_STATION_TAX = {
  outpost:110,
  standard:210,
  advanced:390,
  capital:720
};
function economyIndex(){
  const keys=["copper","iron","gold","crystal","fuel","gas_canister","hull_plate","engine_core","weapon_array"];
  let cur=0,base=0,n=0;
  for(const k of keys){cur+=economy.price(k)||RES_BASE[k]||1;base+=RES_BASE[k]||1;n++;}
  if(!n||!base)return 1;
  return Math.max(0.75,Math.min(1.85,cur/base));
}
function safeZoneId(v){return String(v||"").replace(/[^a-zA-Z0-9_,|:\-]/g,"").slice(0,80);}
function safeCivZoneInput(raw={}){
  const zoneId=safeZoneId(raw.zoneId||raw.id);
  const x=Math.round(Number(raw.x)||0),y=Math.round(Number(raw.y)||0);
  const radius=Math.max(260,Math.min(900,Math.round(Number(raw.radius)||420)));
  const baseStationCount=raw.playerFounded?0:Math.max(2,Math.min(18,Math.floor(Number(raw.baseStationCount ?? raw.stationCount)||5)));
  const name=safeText(raw.name||"Civilization Zone",48)||"Civilization Zone";
  const color=safeText(raw.color||"#ffdd44",16)||"#ffdd44";
  if(!zoneId||!Number.isFinite(x)||!Number.isFinite(y))return null;
  let h=0;for(const c of zoneId)h=(h*33+c.charCodeAt(0))>>>0;
  return {zoneId,x,y,radius,baseStationCount,name,color,superStationLevel:1+(h%4)};
}
// The browser's procedural civilization zones are generated from this same
// seed.  Keep a small server-side mirror for placement validation: otherwise
// a player could found a zone on top of an unowned procedural civilization
// simply because that zone has not yet been purchased and therefore is not in
// `civilizationZones`.
const CLIENT_CIV_CHUNK_SIZE=1250;
function proceduralCivilizationZoneAtChunk(cx,cy){
  if(cx===0&&cy===0)return null;
  const rng=makeRng(`${GALAXY_SEED}|civzone|${cx},${cy}`);
  if(rng()>0.11)return null;
  // Consume the colour draw as the browser does before calculating the
  // position and radius.  The remaining sequence must stay byte-for-byte
  // deterministic with `civilizationZoneForChunk` in public/index.html.
  rng();
  return {
    zoneId:`civ_${cx},${cy}`,
    x:cx*CLIENT_CIV_CHUNK_SIZE+(rng()-.5)*CLIENT_CIV_CHUNK_SIZE*.45,
    y:cy*CLIENT_CIV_CHUNK_SIZE+(rng()-.5)*CLIENT_CIV_CHUNK_SIZE*.45,
    radius:360+rng()*190
  };
}
function civilizationRimPlacementConflict(x,y,radius){
  const requested=Math.max(1,Number(radius)||420);
  // Player-owned / previously bought zones are authoritative records.
  for(const other of civilizationZones.values()){
    if(Math.hypot(x-other.x,y-other.y)<=requested+Math.max(1,Number(other.radius)||420))return other;
  }
  // An unowned procedural zone can be at most 550 units in radius.  Two
  // neighboring chunks plus the current chunk safely cover every rim that can
  // touch a new 420-unit zone, including exact edge contact.
  const baseX=Math.round(x/CLIENT_CIV_CHUNK_SIZE),baseY=Math.round(y/CLIENT_CIV_CHUNK_SIZE);
  for(let cy=baseY-2;cy<=baseY+2;cy++)for(let cx=baseX-2;cx<=baseX+2;cx++){
    const other=proceduralCivilizationZoneAtChunk(cx,cy);
    if(other&&Math.hypot(x-other.x,y-other.y)<=requested+other.radius)return other;
  }
  return null;
}
function civilizationZonePurchaseCost(z){
  const level=Math.max(1,Math.min(10,Number(z.superStationLevel)||Number(z.zoneLevel)||1));
  const raw=(CIV_ZONE_BASE_COST + z.radius*CIV_ZONE_RADIUS_COST + z.baseStationCount*CIV_ZONE_STATION_COST) * (1+(level-1)*.34) * economyIndex();
  return Math.max(65000,Math.round(raw/500)*500);
}
function civilizationZoneStationBuildCost(zone,tier){
  const base=CIV_ZONE_BUILD_BASE_COST[tier]||CIV_ZONE_BUILD_BASE_COST.standard;
  const sizeMult=Math.max(0.9,Math.min(1.6,zone.radius/430));
  const stationMult=1+Math.min(0.75,(zone.builtStations?.length||0)*0.08);
  return Math.round(base*sizeMult*stationMult*economyIndex()/250)*250;
}
function civilizationZoneTaxPerMinute(zone){
  const baseCount=Math.max(1,Math.floor(Number(zone.baseStationCount)||1));
  let tax=CIV_ZONE_SUPER_STATION_TAX + baseCount*CIV_ZONE_BASE_TAX_PER_STATION;
  for(const st of zone.builtStations||[])tax += CIV_ZONE_BUILT_STATION_TAX[st.tier] || CIV_ZONE_BUILT_STATION_TAX.standard;
  return Math.max(250,Math.floor(tax*economyIndex()));
}
function dedupeCivilizationBuiltStations(zone){
  if(!zone||!Array.isArray(zone.builtStations))return [];
  const seen=new Set(),out=[];
  for(const st of zone.builtStations){
    const id=safeZoneId(st?.id||"");
    if(!id||seen.has(id))continue;
    seen.add(id);
    const tier=CIV_STATION_TIERS[st.tier]?st.tier:"standard";
    out.push({...civStationDefaults({tier}),...st,id,x:Math.round(Number(st.x)||zone.x||0),y:Math.round(Number(st.y)||zone.y||0),tier,ownerName:st.ownerName||zone.ownerName||"Owner",createdAt:st.createdAt||Date.now()});
    if(out.length>=30)break;
  }
  zone.builtStations=out;
  return out;
}
function sanitizeStationTasks(raw={}){
  const out={};
  for(const [stationId,t] of Object.entries(raw||{})){
    const id=safeZoneId(stationId);if(!id)continue;
    const task=t?.task==="attack"?"attack":t?.task==="idle"?"idle":"mine";
    out[id]={
      task,
      targetZoneId:task==="attack"?safeZoneId(t.targetZoneId):null,
      targetName:task==="attack"?safeText(t.targetName||"",48):"",
      targetX:task==="attack"?Math.round(Number(t.targetX)||0):0,
      targetY:task==="attack"?Math.round(Number(t.targetY)||0):0,
      targetRadius:task==="attack"?Math.max(0,Math.min(1200,Math.round(Number(t.targetRadius)||0))):0,
      targetColor:task==="attack"?safeText(t.targetColor||"",16):"",
      updatedAt:Math.floor(Number(t.updatedAt)||Date.now()),
      war:task==="attack"&&t?.war===true
    };
  }
  return out;
}
function publicCivilizationStation(st,isOwn){
  if(!st)return null;
  return {id:st.id,x:st.x,y:st.y,tier:st.tier,level:st.level||1,respawnLevel:st.respawnLevel||0,respawnMs:civStationRespawnDelay(st),destroyed:!!st.destroyed,shipCapacity:st.shipCapacity,defaultFleetCount:Number.isFinite(Number(st.defaultFleetCount))?Math.max(0,Math.floor(Number(st.defaultFleetCount))):civDefaultShipCount(st.tier),shipRoster:isOwn?st.shipRoster:[],hp:st.hp,maxHp:st.maxHp,shield:st.shield,maxShield:st.maxShield,resourceTarget:isOwn?st.resourceTarget:null,resourceRates:isOwn?st.resourceRates||{}:{},market:st.market||{},isSuperStation:!!st.isSuperStation};
}
function publicCivilizationZone(zone,viewerId){
  ensureCivLogistics(zone);dedupeCivilizationBuiltStations(zone);zone.stationTasks=sanitizeStationTasks(zone.stationTasks||{});
  const tax=civilizationZoneTaxPerMinute(zone),isOwn=zone.ownerId===viewerId;
  return {
    zoneId:zone.zoneId,name:zone.name,color:zone.color,x:zone.x,y:zone.y,radius:zone.radius,playerFounded:!!zone.playerFounded,
    baseStationCount:zone.baseStationCount,stationCount:zone.baseStationCount+(zone.builtStations?.length||0),
    ownerName:zone.ownerName||null,owned:!!zone.ownerId||!!zone.ownerMemberId,isOwn,
    taxPerMinute:tax,pendingTax:isOwn?Math.floor(zone.pendingTax||0):0,
    stationTasks:isOwn?zone.stationTasks:{},
    factionId:zone.factionId,factionName:zone.factionName,factionBonus:zone.factionBonus,zoneLevel:zone.zoneLevel,stockpileCapacity:zone.stockpileCapacity,turretCapacity:Math.min(20,2+zone.zoneLevel),
    // Aggregate rate/density is intentionally public: nearby zones need it in
    // the contract evaluator, while exact stock and bank balances remain private.
    resourceRates:zone.resourceRates||{},resourceDensity:Number(zone.resourceDensity||0),lastMiningDepositAt:Number(zone.lastMiningDepositAt||0),
    stockpile:isOwn?zone.stockpile:{},stockpileItems:isOwn?zone.stockpileItems:{},bankCredits:isOwn?zone.bankCredits:0,contracts:isOwn?zone.contracts:[],relations:isOwn?zone.relations:{},turrets:isOwn?zone.turrets:[],turretCatalog:CIV_TURRET_CATALOG,
    stationTierCosmetics:{},npcshipCosmeticKey:null,turretCosmeticKey:null,
    superStation:isOwn?{...publicCivilizationStation(zone.superStation,true),task:zone.stationTasks?.[zone.superStation?.id]||{task:"mine"}}:null,
    baseStations:(zone.baseStations||[]).map(st=>({...publicCivilizationStation(st,isOwn),task:isOwn?(zone.stationTasks?.[st.id]||{task:"mine"}):undefined})),
    builtStations:(zone.builtStations||[]).map(st=>({...publicCivilizationStation(st,isOwn),ownerName:zone.ownerName||st.ownerName||"Owner",task:isOwn?(zone.stationTasks?.[st.id]||{task:"mine"}):undefined})),
    stationCosts:Object.fromEntries(["outpost","standard","advanced","capital"].map(t=>[t,civilizationZoneStationBuildCost(zone,t)])),
    zoneUpgradeCost:zone.zoneLevel>=10?null:{credits:25000*(zone.zoneLevel||1),resource:(zone.zoneLevel||1)<4?"iron":(zone.zoneLevel||1)<7?"crystal":"obelisk_core",amount:zone.zoneLevel||1},
    stationUpgradeCosts:{capacity:{credits:8000,resource:"cargo_pod"},health:{credits:8000,resource:"hull_plate"},shield:{credits:8000,resource:"shield_matrix"},respawn:{credits:12000,resource:"engine_core"}}
  };
}
function civilizationZonesFor(viewerId){return [...civilizationZones.values()].map(z=>publicCivilizationZone(z,viewerId));}
function playerOwnsCivilizationZone(p,zone){
  if(!p||!zone)return false;
  return zone.ownerId===p.id || (!!p.memberId && zone.ownerMemberId===p.memberId);
}
function civMineTask(now=Date.now()){return {task:"mine",targetZoneId:null,targetName:"",targetX:0,targetY:0,targetRadius:0,targetColor:"",updatedAt:now,war:false};}
function civIdleTask(now=Date.now()){return {task:"idle",targetZoneId:null,targetName:"",targetX:0,targetY:0,targetRadius:0,targetColor:"",updatedAt:now,war:false};}
function civAttackTask(target,war=false,now=Date.now()){return {task:"attack",targetZoneId:safeZoneId(target?.zoneId||target?.id),targetName:safeText(target?.name||"Target Zone",48),targetX:Math.round(Number(target?.x)||0),targetY:Math.round(Number(target?.y)||0),targetRadius:Math.max(0,Math.round(Number(target?.radius)||0)),targetColor:safeText(target?.color||"",16),updatedAt:now,war:!!war};}
function clearAutomaticCivilizationWarsForOwner(p){
  if(!p)return 0;
  const owned=[...civilizationZones.values()].filter(zone=>playerOwnsCivilizationZone(p,zone));
  const ownedIds=new Set(owned.map(zone=>zone.zoneId));let cleared=0;
  for(const zone of owned){
    ensureCivLogistics(zone);zone.stationTasks=sanitizeStationTasks(zone.stationTasks||{});
    for(const st of civAllStations(zone)){
      const task=zone.stationTasks[st.id];
      if(task?.task==="attack"&&task.war===true&&ownedIds.has(task.targetZoneId)){
        zone.stationTasks[st.id]=civMineTask();cleared++;
      }
    }
    for(const targetId of Object.keys(zone.relations||{})){
      if(!ownedIds.has(targetId))continue;
      const explicitlyAttacking=Object.values(zone.stationTasks||{}).some(task=>task?.task==="attack"&&task.targetZoneId===targetId&&!task.war);
      if(!explicitlyAttacking)zone.relations[targetId]="neutral";
    }
  }
  return cleared;
}
function playerInsideCivilizationZone(p,zone,pad=0){
  if(!p||!zone)return false;
  return Math.hypot(p.x-zone.x,p.y-zone.y) <= (zone.radius||420) + pad;
}
function emitCivilizationZones(socket){socket.emit("civilizationZonesList",civilizationZonesFor(socket.id));}
function broadcastCivilizationZonesList(){for(const [,sock] of io.sockets.sockets)emitCivilizationZones(sock);}
function makeCivilizationZoneRecord(input,p){
  const superStationLevel=1+Math.floor(Math.random()*4);
  const baseStations=[];for(let i=0;i<input.baseStationCount;i++){const tier=["outpost","standard","advanced","capital"][i%4];baseStations.push({...civStationDefaults({tier}),id:`${input.zoneId}|civst|${i}`,tier,ownerName:p.name,createdAt:Date.now()});}
  const zone={...civZoneDefaults({zoneId:input.zoneId,zoneLevel:superStationLevel}),zoneId:input.zoneId,name:input.name,color:input.color,x:input.x,y:input.y,radius:input.radius,baseStationCount:input.baseStationCount,superStationLevel,
    ownerId:p.id,ownerMemberId:p.memberId||null,ownerName:p.name,purchasedAt:Date.now(),baseStations,builtStations:[],stationTasks:{},pendingTax:0,totalTaxCollected:0,stationTierCosmetics:{},npcshipCosmeticKey:null,turretCosmeticKey:null};
  ensureCivLogistics(zone);
  return zone;
}
function randomPointInZone(zone,seedExtra=""){
  const rng=makeRng(`${GALAXY_SEED}|owned-civ-station|${zone.zoneId}|${zone.builtStations?.length||0}|${seedExtra}|${Date.now()}`);
  const a=rng()*Math.PI*2,r=80+rng()*Math.max(120,zone.radius*0.72);
  return {x:Math.round(zone.x+Math.cos(a)*r),y:Math.round(zone.y+Math.sin(a)*r)};
}
function collectPendingCivilizationTaxesFor(p){
  if(!p?.memberId)return;
  let total=0;
  for(const zone of civilizationZones.values()){
    if(zone.ownerMemberId===p.memberId){zone.ownerId=p.id;zone.ownerName=p.name;if(zone.pendingTax>0){total+=Math.floor(zone.pendingTax);zone.pendingTax=0;}}
  }
  if(total>0){p.credits=(p.credits||0)+total;io.to(p.id).emit("civilizationTaxCollected",{credits:p.credits,amount:total,offline:true});persistPlayerSoon(p,"civilization_tax_pending");}
}
function tickCivilizationTaxes(){
  for(const zone of civilizationZones.values()){
    if(!zone.ownerId&&!zone.ownerMemberId)continue;
    const amount=civilizationZoneTaxPerMinute(zone);
    zone.totalTaxCollected=(zone.totalTaxCollected||0)+amount;
    const owner=players.get(zone.ownerId);
    if(owner){
      owner.credits=(owner.credits||0)+amount;
      io.to(owner.id).emit("civilizationTaxCollected",{zoneId:zone.zoneId,zoneName:zone.name,amount,credits:owner.credits,taxPerMinute:amount});
      io.to(owner.id).emit("creditUpdate",{credits:owner.credits});
      persistPlayerSoon(owner,"civilization_zone_tax");
    }else{
      zone.pendingTax=(zone.pendingTax||0)+amount;
    }
  }
  broadcastCivilizationZonesList();
}
function civCargoMineSeconds(capacity,density=0){
  const densityMult=Math.max(.75,Math.min(1.25,1+Math.max(0,Number(density)||0)*.05));
  return Math.max(6,Math.min(56,2*(CIV_LOGISTICS_MINING_BASE_SECONDS+Math.sqrt(Math.max(1,capacity))*CIV_LOGISTICS_MINING_CAPACITY_SCALE)/densityMult));
}
function civCargoReturnSeconds(st,target,craft){
  const distance=target?Math.hypot((Number(target.x)||st.x)-st.x,(Number(target.y)||st.y)-st.y):0;
  const speed=Math.max(60,Number(craft?.speed)||civDefaultShipSpeed(st?.tier));
  return Math.max(CIV_LOGISTICS_MIN_RETURN_SECONDS,Math.min(CIV_LOGISTICS_MAX_RETURN_SECONDS,CIV_LOGISTICS_MIN_RETURN_SECONDS+distance/speed));
}
function civStockpileTotal(zone){return Object.values(zone?.stockpile||{}).reduce((sum,n)=>sum+Math.max(0,Number(n)||0),0);}
function civRandomCargoResource(resources){return resources[Math.floor(Math.random()*resources.length)]||null;}
function civReturnCargo(cargo,st,craft,now){
  if(!cargo)return null;
  cargo.state="returning";
  cargo.returnAt=Math.max(Number(cargo.returnAt)||0,now+Math.round(civCargoReturnSeconds(st,st.resourceTarget,craft)*1000));
  cargo.updatedAt=now;
  return cargo;
}
function tickCivilizationLogistics(){
  const now=Date.now(),tickSeconds=CIV_LOGISTICS_TICK_MS/1000;
  for(const zone of civilizationZones.values()){
    ensureCivLogistics(zone);
    zone.stationTasks=zone.stationTasks||{};
    // The super-station fleet shares the first live mining route selected in
    // its civilization until the player explicitly gives the super station a
    // route. This lets inherited central fleets participate immediately after
    // a zone is purchased without inventing resources that are not on a planet.
    if(!zone.superStation.resourceTarget){
      const firstAssigned=[...(zone.baseStations||[]),...(zone.builtStations||[])].find(st=>st?.resourceTarget?.id);
      if(firstAssigned?.resourceTarget)zone.superStation.resourceTarget={...firstAssigned.resourceTarget};
    }
    const zoneRates={},miningDeliveries=[];let densityTotal=0;
    // Every default and crafted ship—including the super-station fleet—owns an
    // independent cargo record.  The record moves through mining -> returning
    // -> deposited, so the shared stockpile can only increase after a full
    // physical-style haul comes home to its assigned station.
    for(const st of civAllStations(zone)){
      if(st.destroyed){
        st.resourceRates={};st.miningCargo={};
        for(const ship of st.shipRoster||[])if(ship.status!=="destroyed")ship.status="destroyed";
        continue;
      }
      for(const ship of st.shipRoster||[]){
        if(ship.status==="respawning"&&ship.respawnAt<=now)ship.status="active";
        if(ship.status==="active")ship.assignedTask=(zone.stationTasks?.[st.id]?.task)||"mine";
      }
      if(!zone.stationTasks[st.id])zone.stationTasks[st.id]={task:"mine",targetZoneId:null,updatedAt:now};
      const task=zone.stationTasks[st.id]||{task:"mine"};
      st.lastTaskHeartbeat=now;st.resourceRates={};st.miningCargo=st.miningCargo||{};
      const resources=[...new Set((st.resourceTarget?.resources||[]).filter(k=>typeof k==="string"&&k.length))];
      const fleet=civStationMiningFleet(st),fleetIds=new Set(fleet.map(c=>c.id));
      for(const cargoId of Object.keys(st.miningCargo))if(!fleetIds.has(cargoId))delete st.miningCargo[cargoId];
      const density=Math.max(0,Number(st.resourceTarget?.density)||0);
      if(task.task==="mine"&&resources.length)densityTotal+=density;
      for(const craft of fleet){
        const capacity=Math.max(1,Math.floor(Number(craft.capacity)||1));
        let cargo=st.miningCargo[craft.id];
        if(!cargo||(cargo.state!=="returning"&&!resources.includes(cargo.resource)&&task.task==="mine"))cargo={resource:civRandomCargoResource(resources),amount:0,state:"mining",startedAt:now,updatedAt:now};
        cargo.amount=Math.max(0,Math.min(capacity,Number(cargo.amount)||0));
        // An idle recall does not abandon an already loaded haul.  It turns it
        // around and deposits the partial/full cargo once it reaches home.
        if(task.task==="idle"&&cargo.amount>0&&cargo.state!=="returning")civReturnCargo(cargo,st,craft,now);
        if(cargo.state==="returning"){
          if(now>=Number(cargo.returnAt||0)){
            const carrying=Math.max(0,Math.floor(cargo.amount));
            const room=Math.max(0,Math.floor((zone.stockpileCapacity||0)-civStockpileTotal(zone)));
            const delivered=Math.min(room,carrying);
            if(delivered>0&&cargo.resource){
              zone.stockpile[cargo.resource]=(zone.stockpile[cargo.resource]||0)+delivered;
              zone.lastMiningDepositAt=now;
              miningDeliveries.push({stationId:st.id,shipId:craft.id,resourceType:cargo.resource,amount:delivered,capacity});
              cargo.amount=Math.max(0,cargo.amount-delivered);
            }
            if(cargo.amount<=0||task.task!=="mine"||!resources.length){
              cargo={resource:task.task==="mine"?civRandomCargoResource(resources):null,amount:0,state:task.task==="mine"?"mining":"idle",startedAt:now,updatedAt:now};
            }else{
              // Stockpile full: keep the loaded cargo on the returning ship and
              // retry without producing or deleting resources.
              cargo.returnAt=now+1000;cargo.updatedAt=now;
            }
          }
          st.miningCargo[craft.id]=cargo;
          continue;
        }
        if(task.task!=="mine"||!resources.length){
          if(task.task==="attack")delete st.miningCargo[craft.id];
          else st.miningCargo[craft.id]={...cargo,state:"idle",updatedAt:now};
          continue;
        }
        if(!resources.includes(cargo.resource))cargo.resource=civRandomCargoResource(resources);
        const mineSeconds=civCargoMineSeconds(capacity,density),returnSeconds=civCargoReturnSeconds(st,st.resourceTarget,craft);
        const perResourceRate=(capacity*60/(mineSeconds+returnSeconds))/Math.max(1,resources.length);
        for(const resource of resources){
          st.resourceRates[resource]=(st.resourceRates[resource]||0)+perResourceRate;
          zoneRates[resource]=(zoneRates[resource]||0)+perResourceRate;
        }
        cargo.state="mining";
        cargo.amount=Math.min(capacity,cargo.amount+(capacity/mineSeconds)*tickSeconds);
        cargo.updatedAt=now;
        if(cargo.amount>=capacity-.0001){cargo.amount=capacity;civReturnCargo(cargo,st,craft,now);}
        st.miningCargo[craft.id]=cargo;
      }
    }
    zone.resourceRates=Object.fromEntries(Object.entries(zoneRates).map(([k,v])=>[k,Number(v.toFixed(2))]));
    zone.resourceDensity=Number(densityTotal.toFixed(2));
    // The full zone list remains a useful periodic recovery path, but this
    // direct event makes the stockpile UI update on every completed haul.
    const miningOwner=zone.ownerId?players.get(zone.ownerId):null;
    if(miningOwner&&miningDeliveries.length){
      const stockpileTotal=civStockpileTotal(zone);
      // One immediate, complete snapshot per haul makes the master-stockpile
      // panel authoritative even while it is already open.  The client does
      // not need to close/reopen a menu or wait for the periodic zone list.
      for(const delivery of miningDeliveries)io.to(miningOwner.id).emit("civilizationStockpileDeposit",{zoneId:zone.zoneId,stationId:delivery.stationId,shipId:delivery.shipId,resourceType:delivery.resourceType,amount:delivery.amount,capacity:delivery.capacity,stockpile:{...zone.stockpile},stockpileTotal,stockpileCapacity:zone.stockpileCapacity,resourceRates:{...zone.resourceRates},lastMiningDepositAt:zone.lastMiningDepositAt});
      // Save completed hauls promptly without attempting a network write for
      // every individual ship.  This keeps stockpile gains safe on reconnects
      // while still coalescing busy fleets into a single snapshot.
      if(now-(zone.lastLogisticsPersistAt||0)>=8000){
        zone.lastLogisticsPersistAt=now;
        persistPlayerSoon(miningOwner,"civilization_stockpile_delivery",600);
      }
    }
    for(const c of zone.contracts||[]){
      if(c.incoming)continue;
      if(c.status==="pending"&&c.decisionAt<=now){c.status=(c.fairness||0)>=.5?"active":"declined";if(c.status==="active")zone.relations[c.targetZoneId]="ally";}
      if(c.status!=="active")continue;
      const g=c.give||{},r=c.receive||{},target=civilizationZones.get(c.targetZoneId);let payable=true;if(g.credits&&zone.bankCredits<g.credits)payable=false;if(g.type&&g.amount&&(zone.stockpile[g.type]||0)<g.amount)payable=false;if(!payable){c.status="paused";c.pauseReason="Insufficient bank or stockpile";continue;}if(g.credits)zone.bankCredits-=g.credits;if(g.type&&g.amount)zone.stockpile[g.type]-=g.amount;
      if(target){ensureCivLogistics(target);if(g.credits)target.bankCredits+=g.credits;if(g.type&&g.amount)target.stockpile[g.type]=(target.stockpile[g.type]||0)+g.amount;if(r.credits&&target.bankCredits>=r.credits){target.bankCredits-=r.credits;zone.bankCredits+=r.credits;}if(r.type&&r.amount&&(target.stockpile[r.type]||0)>=r.amount){target.stockpile[r.type]-=r.amount;zone.stockpile[r.type]=(zone.stockpile[r.type]||0)+r.amount;}}else{if(r.credits)zone.bankCredits+=r.credits;if(r.type&&r.amount)zone.stockpile[r.type]=(zone.stockpile[r.type]||0)+r.amount;}
      c.lastDeliveryAt=now;c.deliveryStatus="NPC convoy dispatched";
    }
    // Mining runs continuously, so checkpoint the authoritative zone state on
    // a modest cadence as well.  This keeps full-cargo deposits and live
    // rates from being lost between unrelated player actions.
    if(zone.ownerId&&now-(zone.lastLogisticsPersistAt||0)>=30000){
      const owner=players.get(zone.ownerId);
      if(owner){zone.lastLogisticsPersistAt=now;persistPlayerSoon(owner,"civilization_logistics",1800);}
    }
  }
  broadcastCivilizationZonesList();
}


/* ── Player-built station defense stats ── */
function stationDefenseStats(tier){
  const table={
    outpost:{maxHp:3500,maxShield:1400,shieldRegen:18,hpRegen:2,respawnDelay:16000,defenseWindow:45000,xpReward:300},
    base:{maxHp:9000,maxShield:3600,shieldRegen:34,hpRegen:5,respawnDelay:13000,defenseWindow:55000,xpReward:750},
    fortress:{maxHp:18000,maxShield:8000,shieldRegen:60,hpRegen:9,respawnDelay:10000,defenseWindow:70000,xpReward:1600}
  };
  return table[tier]||table.outpost;
}
function makeStationState(tier){
  const stats=stationDefenseStats(tier);
  return {hp:stats.maxHp,maxHp:stats.maxHp,shield:stats.maxShield,maxShield:stats.maxShield,shieldRegenTimer:0,underAttackUntil:0,destroyed:false,destroyedAt:0};
}
function applyStationDamage(st,rawDamage){
  const raw=Math.max(0,Math.min(900,Number(rawDamage)||0));
  if(raw<=0||st.destroyed)return {damage:0,hpDamage:0,shieldDamage:0,destroyed:false};
  let dmg=raw,shieldDamage=0,hpDamage=0;
  if(st.shield>0){shieldDamage=Math.min(st.shield,dmg);st.shield-=shieldDamage;dmg-=shieldDamage;}
  if(dmg>0){hpDamage=Math.min(st.hp,dmg);st.hp=Math.max(0,st.hp-hpDamage);}
  st.shieldRegenTimer=8;
  const stats=stationDefenseStats(st.tier);
  st.underAttackUntil=Date.now()+stats.defenseWindow;
  return {damage:raw,hpDamage,shieldDamage,destroyed:st.hp<=0};
}
function tickOwnedStationDefense(dt){
  const now=Date.now();
  for(const[,st]of ownedStations){
    const stats=stationDefenseStats(st.tier);
    if(!Number.isFinite(st.hp)){Object.assign(st,makeStationState(st.tier));}
    if(st.destroyed)continue;
    st.shieldRegenTimer=Math.max(0,(st.shieldRegenTimer||0)-dt);
    if(st.shieldRegenTimer<=0&&st.shield<st.maxShield)st.shield=Math.min(st.maxShield,st.shield+stats.shieldRegen*dt);
    if(st.shieldRegenTimer<=0&&st.hp<st.maxHp)st.hp=Math.min(st.maxHp,st.hp+stats.hpRegen*dt);
    for(const ship of st.hiredShips){
      if(ship.state==="respawning"&&ship.respawnAt&&ship.respawnAt<=now){ship.state="defending";ship.respawnAt=0;ship.cargo=ship.cargo||{};}
      if(now<st.underAttackUntil&&ship.state!=="respawning")ship.state="defending";
    }
  }
}
function destroyOwnedStation(st,attacker){
  if(st.destroyed)return;
  st.destroyed=true;st.destroyedAt=Date.now();st.hp=0;st.shield=0;st.underAttackUntil=Date.now()+30000;
  for(const ship of st.hiredShips){if(ship.state!=="respawning")ship.state="defending";}
  const goods={...st.accumulatedGoods};st.accumulatedGoods={};
  if(attacker){addScore(attacker,stationDefenseStats(st.tier).xpReward,"Station Destroyed");}
  io.emit("ownedStationDestroyed",{stationKey:st.key,x:st.x,y:st.y,tier:st.tier,ownerName:st.ownerName,goods,destroyedBy:attacker?.name||"Unknown"});
  broadcastChat("Server",`${attacker?.name||"A raider"} destroyed ${st.ownerName}'s ${OWNED_STATION_TIERS[st.tier]?.name||st.tier}!`,"#ff5544");
}



/* ── Cosmetics + coupon shop ── */
const COSMETIC_DEFS = {
  ship_nebula_wing:{key:"ship_nebula_wing",slot:"ship",name:"Nebula Wing Hull",price:250000,description:"Purple-blue nebula plating with soft glow and swept wings.",color:"#9d7bff",accent:"#7be6ff",shape:"nebula"},
  ship_solar_royal:{key:"ship_solar_royal",slot:"ship",name:"Solar Royal Hull",price:750000,description:"Gold solar armor with crown-like fins.",color:"#ffdd44",accent:"#fff0a8",shape:"royal"},
  ship_void_chrome:{key:"ship_void_chrome",slot:"ship",name:"Void Chrome Hull",price:1500000,description:"Dark chrome ship body with cyan blade trim.",color:"#101827",accent:"#7be6ff",shape:"blade"},
  ship_aether_flame:{key:"ship_aether_flame",slot:"ship",name:"Aether Flame Hull",price:3000000,description:"Flame-lined starship plating with ember wings.",color:"#ff6b35",accent:"#ffdd44",shape:"flame"},
  ship_crystal_lancer:{key:"ship_crystal_lancer",slot:"ship",name:"Crystal Lancer Hull",price:1750000,description:"Long crystalline spear-nose frame.",color:"#7be6ff",accent:"#e9fbff",shape:"lancer"},
  ship_orbital_mantis:{key:"ship_orbital_mantis",slot:"ship",name:"Orbital Mantis Hull",price:2400000,description:"Hooked wing cutter with mantis-like prongs.",color:"#78ff8a",accent:"#d6ff7b",shape:"mantis"},
  ship_stingray:{key:"ship_stingray",slot:"ship",name:"Stingray Cruiser Hull",price:3200000,description:"Wide gliding ray design with glowing tail engines.",color:"#58a6ff",accent:"#b9f3ff",shape:"stingray"},
  ship_obelisk_elite:{key:"ship_obelisk_elite",slot:"ship",name:"Obelisk Elite Hull",price:5200000,description:"Tall carrier silhouette with an obelisk core.",color:"#1b1330",accent:"#cc88ff",shape:"obeliskElite"},
  bullet_ion_rain:{key:"bullet_ion_rain",slot:"bullet",name:"Ion Rain Bullets",price:400000,description:"Bright cyan projectile trail.",color:"#7be6ff",sizeBoost:0.2},
  bullet_lux_beam:{key:"bullet_lux_beam",slot:"bullet",name:"Lux Beam Bullets",price:950000,description:"Golden laser bolt style.",color:"#ffdd44",sizeBoost:0.45},
  bullet_shadow_orb:{key:"bullet_shadow_orb",slot:"bullet",name:"Shadow Orb Bullets",price:1800000,description:"Purple shadow-orb projectiles.",color:"#cc88ff",sizeBoost:1.0},
  bullet_prismatic:{key:"bullet_prismatic",slot:"bullet",name:"Prismatic Bullets",price:4500000,description:"Premium rainbow starfire bullets.",color:"#ffffff",rainbow:true,sizeBoost:0.8},
  enemy_neon_outline:{key:"enemy_neon_outline",slot:"enemy",name:"Neon Enemy Outline",price:1250000,description:"Turns hostile raiders into angular neon outline ships.",color:"#ff5cff",accent:"#7be6ff",shape:"outline"},
  enemy_crimson_raid:{key:"enemy_crimson_raid",slot:"enemy",name:"Crimson Raider Pack",price:2500000,description:"Crimson enemy projectiles and fang-shaped raider hulls.",color:"#ff3344",accent:"#ffdd44",shape:"fang"},
  enemy_void_bats:{key:"enemy_void_bats",slot:"enemy",name:"Void Bat Enemy Ships",price:3400000,description:"Bat-wing hostile ships with dark violet cores.",color:"#7f4dff",accent:"#ff5cff",shape:"bat"},
  enemy_gold_hunters:{key:"enemy_gold_hunters",slot:"enemy",name:"Gold Hunter Enemy Ships",price:4200000,description:"Gold-trim hunter enemies with forked noses.",color:"#ffdd44",accent:"#ff8844",shape:"hunter"},
  particle_star_spark:{key:"particle_star_spark",slot:"particle",name:"Star Spark Particles",price:350000,description:"Sparkly star muzzle particles.",color:"#fff0a8"},
  particle_aether_flame:{key:"particle_aether_flame",slot:"particle",name:"Aether Flame Particles",price:1750000,description:"Warm flame exhaust and shot particles.",color:"#ff8844"},
  particle_cosmic_bloom:{key:"particle_cosmic_bloom",slot:"particle",name:"Cosmic Bloom Particles",price:5000000,description:"Luxury cosmic bloom particle style.",color:"#cc88ff",accent:"#7be6ff"},
  trail_comet_tail:{key:"trail_comet_tail",slot:"trail",name:"Comet Tail Trail",price:700000,description:"Comet exhaust trail for boosted travel.",color:"#b9f3ff"},
  trail_gold_dust:{key:"trail_gold_dust",slot:"trail",name:"Gold Dust Trail",price:2200000,description:"Premium golden engine trail.",color:"#ffdd44"},
  station_neon_ring:{key:"station_neon_ring",slot:"station",name:"Neon Ring Stations",price:1800000,description:"Space stations become glowing ring hubs.",color:"#7be6ff",accent:"#ff5cff",shape:"ring"},
  station_crystal_citadel:{key:"station_crystal_citadel",slot:"station",name:"Crystal Citadel Stations",price:2600000,description:"Stations redraw as faceted crystal citadels.",color:"#b9f3ff",accent:"#ffffff",shape:"crystal"},
  station_solar_fortress:{key:"station_solar_fortress",slot:"station",name:"Solar Fortress Stations",price:3600000,description:"Stations gain armored golden fortress plating.",color:"#ffdd44",accent:"#ff8844",shape:"fortress"},
  station_void_spire:{key:"station_void_spire",slot:"station",name:"Void Spire Stations",price:4800000,description:"Stations become dark spires with a violet core.",color:"#221833",accent:"#cc88ff",shape:"spire"},
  planet_lush_worlds:{key:"planet_lush_worlds",slot:"planet",name:"Lush Planet Designs",price:1500000,description:"Planets redraw with green-blue living world bands.",color:"#78ff8a",accent:"#7be6ff",shape:"lush"},
  planet_crystal_worlds:{key:"planet_crystal_worlds",slot:"planet",name:"Crystal Planet Designs",price:2400000,description:"Planets gain crystal facets and bright ice rings.",color:"#7be6ff",accent:"#ffffff",shape:"crystal"},
  planet_lava_worlds:{key:"planet_lava_worlds",slot:"planet",name:"Lava Planet Designs",price:3200000,description:"Planets redraw with magma cracks and ember glow.",color:"#ff6b35",accent:"#ffdd44",shape:"lava"},
  planet_void_worlds:{key:"planet_void_worlds",slot:"planet",name:"Void Planet Designs",price:4300000,description:"Planets become dark eclipse worlds with purple rings.",color:"#1b1330",accent:"#cc88ff",shape:"void"},

  ship_aurora_saber:{key:"ship_aurora_saber",slot:"ship",name:"Aurora Saber Hull",price:2800000,description:"A slim aurora-lit saber frame with bright teal wing edges.",color:"#3affd0",accent:"#fff0a8",shape:"lancer"},
  ship_ruby_vector:{key:"ship_ruby_vector",slot:"ship",name:"Ruby Vector Hull",price:3600000,description:"Red vector-plated racer hull with neon blade trim.",color:"#ff335d",accent:"#ffcc44",shape:"blade"},
  ship_quantum_ray:{key:"ship_quantum_ray",slot:"ship",name:"Quantum Ray Hull",price:4400000,description:"Wide manta-ray silhouette with quantum blue glow.",color:"#45a3ff",accent:"#7bffea",shape:"stingray"},
  ship_codex_crown:{key:"ship_codex_crown",slot:"ship",name:"Codex Crown Hull",price:6500000,description:"Prestige crown-class ship body for late-game pilots.",color:"#ffe66d",accent:"#ff5cff",shape:"royal"},
  bullet_ember_bolts:{key:"bullet_ember_bolts",slot:"bullet",name:"Ember Bolts",price:650000,description:"Orange ember projectiles with a hot core.",color:"#ff8844",accent:"#ffdd44",sizeBoost:0.3},
  bullet_arc_lime:{key:"bullet_arc_lime",slot:"bullet",name:"Arc Lime Shots",price:1350000,description:"Electric green shot style with a sharper glow.",color:"#78ff8a",accent:"#d6ff7b",sizeBoost:0.55},
  bullet_blue_nova:{key:"bullet_blue_nova",slot:"bullet",name:"Blue Nova Rounds",price:2600000,description:"Deep-blue nova shots with a larger impact profile.",color:"#58a6ff",accent:"#b9f3ff",sizeBoost:0.75},
  bullet_heart_star:{key:"bullet_heart_star",slot:"bullet",name:"Heart Star Shots",price:5200000,description:"Luxury pink starfire projectile style.",color:"#ff77dd",accent:"#fff0ff",sizeBoost:0.95},
  enemy_aqua_reavers:{key:"enemy_aqua_reavers",slot:"enemy",name:"Aqua Reaver Enemies",price:1850000,description:"Enemy raiders shift into aqua razor silhouettes.",color:"#35e7ff",accent:"#ffffff",shape:"fang"},
  enemy_ember_wasps:{key:"enemy_ember_wasps",slot:"enemy",name:"Ember Wasp Enemies",price:3100000,description:"Hostile ships become hot orange wasp-like attackers.",color:"#ff8844",accent:"#ffdd44",shape:"hunter"},
  enemy_emerald_stalkers:{key:"enemy_emerald_stalkers",slot:"enemy",name:"Emerald Stalker Enemies",price:3900000,description:"Green stealth enemy visual pack with sharp wings.",color:"#78ff8a",accent:"#0dffb2",shape:"bat"},
  enemy_codex_phantoms:{key:"enemy_codex_phantoms",slot:"enemy",name:"Codex Phantom Enemies",price:5600000,description:"Rare phantom enemy silhouettes with violet neon outlines.",color:"#b86bff",accent:"#7be6ff",shape:"outline"},
  npcship_trader_teal:{key:"npcship_trader_teal",slot:"npcship",name:"Teal NPC Trade Ships",price:900000,description:"Friendly and neutral NPC trade ships use teal courier hulls.",color:"#7be6ff",accent:"#ffffff",shape:"hauler"},
  npcship_solar_barge:{key:"npcship_solar_barge",slot:"npcship",name:"Solar NPC Barges",price:1750000,description:"NPC trade ships become gold solar barges.",color:"#ffdd44",accent:"#ff8844",shape:"hauler"},
  npcship_crystal_courier:{key:"npcship_crystal_courier",slot:"npcship",name:"Crystal NPC Couriers",price:2900000,description:"NPC couriers gain crystalline blue lancer hulls.",color:"#b9f3ff",accent:"#7be6ff",shape:"lancer"},
  npcship_void_caravan:{key:"npcship_void_caravan",slot:"npcship",name:"Void NPC Caravans",price:4700000,description:"NPC trade ships become dark caravan escorts with violet cores.",color:"#26143f",accent:"#cc88ff",shape:"stingray"},
  particle_neon_snow:{key:"particle_neon_snow",slot:"particle",name:"Neon Snow Particles",price:900000,description:"Cool blue-white twinkle particles.",color:"#dff9ff",accent:"#7be6ff"},
  particle_green_matrix:{key:"particle_green_matrix",slot:"particle",name:"Green Matrix Particles",price:2600000,description:"Matrix-green digital spark particles.",color:"#78ff8a",accent:"#d6ff7b"},
  particle_royal_prism:{key:"particle_royal_prism",slot:"particle",name:"Royal Prism Particles",price:6200000,description:"Prismatic prestige sparks for shots and exhaust.",color:"#ffffff",accent:"#ff5cff"},
  trail_aqua_wake:{key:"trail_aqua_wake",slot:"trail",name:"Aqua Wake Trail",price:1100000,description:"Bright aqua engine wake for travel.",color:"#7be6ff",accent:"#ffffff"},
  trail_ember_stream:{key:"trail_ember_stream",slot:"trail",name:"Ember Stream Trail",price:3000000,description:"Orange ember exhaust stream.",color:"#ff8844",accent:"#ffdd44"},
  trail_prism_comet:{key:"trail_prism_comet",slot:"trail",name:"Prism Comet Trail",price:7000000,description:"Prestige rainbow comet exhaust.",color:"#ffffff",accent:"#ff5cff",rainbow:true},
  station_aqua_array:{key:"station_aqua_array",slot:"station",name:"Aqua Array Stations",price:2200000,description:"Stations gain clean aqua array arms.",color:"#0f3450",accent:"#7be6ff",shape:"ring"},
  station_emerald_gate:{key:"station_emerald_gate",slot:"station",name:"Emerald Gate Stations",price:3900000,description:"Stations redraw as green gate fortresses.",color:"#123522",accent:"#78ff8a",shape:"fortress"},
  station_royal_obelisk:{key:"station_royal_obelisk",slot:"station",name:"Royal Obelisk Stations",price:6500000,description:"Prestige obelisk stations with gold-violet cores.",color:"#1b1330",accent:"#ffdd44",shape:"spire"},
  planet_ocean_worlds:{key:"planet_ocean_worlds",slot:"planet",name:"Ocean Planet Designs",price:1900000,description:"Planets redraw as blue ocean worlds with pale rings.",color:"#2f8dff",accent:"#b9f3ff",shape:"lush"},
  planet_emerald_worlds:{key:"planet_emerald_worlds",slot:"planet",name:"Emerald Planet Designs",price:3000000,description:"Planets gain luminous emerald bands.",color:"#24b86b",accent:"#78ff8a",shape:"lush"},
  planet_royal_worlds:{key:"planet_royal_worlds",slot:"planet",name:"Royal Planet Designs",price:6200000,description:"Prestige gold-violet planet palette.",color:"#ffdd44",accent:"#cc88ff",shape:"crystal"}
  ,
  engine_blue_star:{key:"engine_blue_star",slot:"engine",name:"Blue Star Engine Core",price:1250000,description:"Blue-white engine flare for player and equipped cosmetic ships.",color:"#58a6ff",accent:"#dff9ff",shape:"flare"},
  engine_ember_core:{key:"engine_ember_core",slot:"engine",name:"Ember Engine Core",price:2400000,description:"Warm orange engine plume and boosted thrust glow.",color:"#ff8844",accent:"#ffdd44",shape:"flare"},
  engine_emerald_core:{key:"engine_emerald_core",slot:"engine",name:"Emerald Engine Core",price:3600000,description:"Green plasma engine flare for a clean eco-tech look.",color:"#78ff8a",accent:"#d6ff7b",shape:"flare"},
  engine_void_reactor:{key:"engine_void_reactor",slot:"engine",name:"Void Reactor Engines",price:5800000,description:"Dark purple reactor plume with violet edge glow.",color:"#b86bff",accent:"#ff5cff",shape:"flare"},
  shield_aqua_ring:{key:"shield_aqua_ring",slot:"shield",name:"Aqua Shield Ring",price:1400000,description:"A cyan circular shield aura around your ship while shields are active.",color:"#7be6ff",accent:"#dff9ff",shape:"ring"},
  shield_gold_halo:{key:"shield_gold_halo",slot:"shield",name:"Gold Halo Shield",price:2900000,description:"Gold shield aura for prestige pilots.",color:"#ffdd44",accent:"#fff0a8",shape:"ring"},
  shield_crimson_guard:{key:"shield_crimson_guard",slot:"shield",name:"Crimson Guard Shield",price:4200000,description:"Red-orange combat shield aura with angular pulses.",color:"#ff5544",accent:"#ffcc66",shape:"angular"},
  shield_prism_barrier:{key:"shield_prism_barrier",slot:"shield",name:"Prism Barrier Shield",price:7000000,description:"Late-game rainbow-tinted shield shimmer.",color:"#ffffff",accent:"#ff5cff",rainbow:true,shape:"ring"},
  suit_orange_miner:{key:"suit_orange_miner",slot:"suit",name:"Orange Miner Suit",price:650000,description:"Planetside astronaut suit with a classic orange work pack.",color:"#ff8844",accent:"#dff9ff",shape:"suit"},
  suit_teal_ranger:{key:"suit_teal_ranger",slot:"suit",name:"Teal Ranger Suit",price:1250000,description:"Cool teal planetside explorer suit.",color:"#7be6ff",accent:"#78ff8a",shape:"suit"},
  suit_gold_captain:{key:"suit_gold_captain",slot:"suit",name:"Gold Captain Suit",price:2600000,description:"Gold-accent planetside captain suit.",color:"#ffdd44",accent:"#7be6ff",shape:"suit"},
  suit_void_runner:{key:"suit_void_runner",slot:"suit",name:"Void Runner Suit",price:4200000,description:"Dark violet planetside suit with luminous visor accents.",color:"#221833",accent:"#cc88ff",shape:"suit"},
  laser_mining_cyan:{key:"laser_mining_cyan",slot:"laser",name:"Cyan Mining Beam",price:900000,description:"Changes planetside mining beam highlights to bright cyan.",color:"#7be6ff",accent:"#ffffff",shape:"beam"},
  laser_mining_gold:{key:"laser_mining_gold",slot:"laser",name:"Gold Mining Beam",price:1800000,description:"Gold mining beam and targeting highlight for planetside mining.",color:"#ffdd44",accent:"#fff0a8",shape:"beam"},
  laser_mining_lime:{key:"laser_mining_lime",slot:"laser",name:"Lime Mining Beam",price:2800000,description:"Green eco-laser mining beam with brighter target feedback.",color:"#78ff8a",accent:"#d6ff7b",shape:"beam"},
  laser_mining_prism:{key:"laser_mining_prism",slot:"laser",name:"Prism Mining Beam",price:5600000,description:"Premium rainbow prism mining beam style.",color:"#ffffff",accent:"#ff5cff",rainbow:true,shape:"beam"},
  ship_pixel_runner:{key:"ship_pixel_runner",slot:"ship",name:"Pixel Runner Hull",price:3900000,description:"Retro blocky racer hull inspired by 16-bit space shooters.",color:"#7be6ff",accent:"#ffdd44",shape:"blade"},
  ship_emerald_falcon:{key:"ship_emerald_falcon",slot:"ship",name:"Emerald Falcon Hull",price:4900000,description:"Green falcon-style spread-wing frame.",color:"#78ff8a",accent:"#d6ff7b",shape:"mantis"},
  npcship_pixel_haulers:{key:"npcship_pixel_haulers",slot:"npcship",name:"Pixel NPC Haulers",price:2500000,description:"NPC trade ships get chunky retro hauler silhouettes.",color:"#58a6ff",accent:"#ffdd44",shape:"hauler"},
  npcship_emerald_convoy:{key:"npcship_emerald_convoy",slot:"npcship",name:"Emerald NPC Convoys",price:3800000,description:"NPC trade convoys use green-lit eco cargo hulls.",color:"#78ff8a",accent:"#d6ff7b",shape:"hauler"},
  station_pixel_arcade:{key:"station_pixel_arcade",slot:"station",name:"Pixel Arcade Stations",price:5200000,description:"Stations adopt a chunkier retro arcade silhouette.",color:"#162a44",accent:"#7be6ff",shape:"ring"},
  planet_retro_grid_worlds:{key:"planet_retro_grid_worlds",slot:"planet",name:"Retro Grid Planets",price:4800000,description:"Planets gain bold retro grid bands and bright blue rings.",color:"#0f3450",accent:"#7be6ff",shape:"crystal"},
  bullet_pixel_stars:{key:"bullet_pixel_stars",slot:"bullet",name:"Pixel Star Shots",price:3400000,description:"Blockier pixel-star projectile look.",color:"#fff0a8",accent:"#7be6ff",sizeBoost:0.65},
  trail_pixel_sparks:{key:"trail_pixel_sparks",slot:"trail",name:"Pixel Spark Trail",price:3300000,description:"Chunkier retro spark exhaust trail.",color:"#7be6ff",accent:"#ffdd44"},
  particle_pixel_pop:{key:"particle_pixel_pop",slot:"particle",name:"Pixel Pop Particles",price:2100000,description:"Chunky pop particles for shots and impact feedback.",color:"#ffdd44",accent:"#7be6ff"},
  enemy_pixel_raiders:{key:"enemy_pixel_raiders",slot:"enemy",name:"Pixel Raider Enemies",price:4600000,description:"Enemies use bolder arcade-like silhouettes and neon edges.",color:"#ff5544",accent:"#ffdd44",shape:"fang"}
,
  ship_codex_sentinel:{key:"ship_codex_sentinel",slot:"ship",name:"Codex Sentinel Hull",price:8800000,description:"Angular neon-codex sentinel plating with twin energy fins.",color:"#00f0ff",accent:"#ffdd44",shape:"lancer"},
  ship_void_bloom:{key:"ship_void_bloom",slot:"ship",name:"Void Bloom Hull",price:9300000,description:"Dark floral void frame with magenta bloom wings.",color:"#201030",accent:"#ff77dd",shape:"flame"},
  bullet_codex_runes:{key:"bullet_codex_runes",slot:"bullet",name:"Codex Rune Shots",price:5800000,description:"Runic cyan-gold projectile style for high-tier pilots.",color:"#7be6ff",accent:"#ffdd44",sizeBoost:0.88},
  bullet_void_sparks:{key:"bullet_void_sparks",slot:"bullet",name:"Void Spark Shots",price:6400000,description:"Dark-matter purple bolts with pink spark cores.",color:"#8d5cff",accent:"#ff77dd",sizeBoost:0.92},
  enemy_neon_serpents:{key:"enemy_neon_serpents",slot:"enemy",name:"Neon Serpent Enemies",price:6200000,description:"Enemy ships use long neon serpent silhouettes.",color:"#78ff8a",accent:"#7be6ff",shape:"bat"},
  enemy_void_spawn:{key:"enemy_void_spawn",slot:"enemy",name:"Void Spawn Enemies",price:7800000,description:"Hostile ships shift into dark void-spawn outlines.",color:"#4b2a7f",accent:"#ff77dd",shape:"outline"},
  npcship_codex_freighters:{key:"npcship_codex_freighters",slot:"npcship",name:"Codex NPC Freighters",price:5200000,description:"NPC trade ships use neon-codex freighter hulls.",color:"#0fd8ff",accent:"#ffdd44",shape:"hauler"},
  station_codex_gate:{key:"station_codex_gate",slot:"station",name:"Codex Gate Stations",price:7600000,description:"Stations become symmetrical codex gates with teal-gold cores.",color:"#062033",accent:"#7be6ff",shape:"ring"},
  station_void_anchor:{key:"station_void_anchor",slot:"station",name:"Void Anchor Stations",price:8200000,description:"Stations become violet-black anchors in space.",color:"#170d26",accent:"#cc88ff",shape:"spire"},
  planet_codex_neon_worlds:{key:"planet_codex_neon_worlds",slot:"planet",name:"Codex Neon Planet Designs",price:7200000,description:"Planets draw with neon grid bands and codex cyan-gold accents.",color:"#0fd8ff",accent:"#ffdd44",shape:"crystal"},
  planet_void_spawn_worlds:{key:"planet_void_spawn_worlds",slot:"planet",name:"Void Spawn Planet Designs",price:8400000,description:"Planets become shadowed void-spawn worlds with magenta eclipse rings.",color:"#1a0d2e",accent:"#ff77dd",shape:"void"},
  engine_codex_afterburn:{key:"engine_codex_afterburn",slot:"engine",name:"Codex Afterburn Engines",price:7800000,description:"Teal-gold afterburn plumes with rune sparks.",color:"#7be6ff",accent:"#ffdd44",shape:"flare"},
  shield_void_shell:{key:"shield_void_shell",slot:"shield",name:"Void Shell Shield",price:7900000,description:"Dark violet defensive shell with magenta edge pulses.",color:"#3c1d66",accent:"#ff77dd",shape:"angular"},
  suit_codex_pilot:{key:"suit_codex_pilot",slot:"suit",name:"Codex Pilot Suit",price:5600000,description:"Planetside codex pilot armor with bright cyan visor trim.",color:"#0f3450",accent:"#7be6ff",shape:"suit"},
  laser_void_cutter:{key:"laser_void_cutter",slot:"laser",name:"Void Cutter Mining Beam",price:6200000,description:"Void-magenta mining cutter beam for planetside work.",color:"#cc88ff",accent:"#ff77dd",shape:"beam"}
};
Object.assign(COSMETIC_DEFS,{
  ship_titan_orchid:{key:"ship_titan_orchid",slot:"ship",name:"Titan Orchid Hull",price:7600000,description:"A broad-petal prestige hull with neon magenta bloom fins.",color:"#ff77dd",accent:"#ffd0ff",shape:"flame"},
  ship_glacier_prism:{key:"ship_glacier_prism",slot:"ship",name:"Glacier Prism Hull",price:5300000,description:"Icy prism hull with luminous polar edges.",color:"#dff9ff",accent:"#58a6ff",shape:"lancer"},
  bullet_grape_pop:{key:"bullet_grape_pop",slot:"bullet",name:"Grape Pop Shots",price:2100000,description:"Violet pop-shot bullets with a candy-bright flash.",color:"#c77dff",accent:"#fff0ff",sizeBoost:0.55},
  bullet_solar_sparks:{key:"bullet_solar_sparks",slot:"bullet",name:"Solar Spark Shots",price:3900000,description:"Starry yellow-orange projectiles with brighter core sparks.",color:"#ffdd44",accent:"#ff8844",sizeBoost:0.78},
  enemy_cobalt_hounds:{key:"enemy_cobalt_hounds",slot:"enemy",name:"Cobalt Hound Enemies",price:2800000,description:"Enemy ships become streamlined cobalt pursuit craft.",color:"#58a6ff",accent:"#dff9ff",shape:"hunter"},
  enemy_rose_reavers:{key:"enemy_rose_reavers",slot:"enemy",name:"Rose Reaver Enemies",price:5100000,description:"Rose-pink outlaw silhouettes with sharp neon wing tips.",color:"#ff77dd",accent:"#ffdd44",shape:"fang"},
  npcship_royal_mail:{key:"npcship_royal_mail",slot:"npcship",name:"Royal Mail Convoys",price:4200000,description:"NPC trade convoys use gold-violet courier hulls.",color:"#ffdd44",accent:"#cc88ff",shape:"hauler"},
  particle_sun_glitter:{key:"particle_sun_glitter",slot:"particle",name:"Sun Glitter Particles",price:1800000,description:"Warm solar twinkle particles for impacts and fire.",color:"#fff0a8",accent:"#ff8844"},
  particle_void_confetti:{key:"particle_void_confetti",slot:"particle",name:"Void Confetti Particles",price:4100000,description:"Chaotic purple confetti sparks for a playful premium hit effect.",color:"#cc88ff",accent:"#ff77dd"},
  trail_starlace:{key:"trail_starlace",slot:"trail",name:"Starlace Trail",price:4800000,description:"Elegant sparkling starlace wake behind the ship.",color:"#ffffff",accent:"#7be6ff"},
  trail_cobalt_fume:{key:"trail_cobalt_fume",slot:"trail",name:"Cobalt Fume Trail",price:1750000,description:"Deep blue exhaust stream with glowing edges.",color:"#58a6ff",accent:"#dff9ff"},
  station_aurora_hub:{key:"station_aurora_hub",slot:"station",name:"Aurora Hub Stations",price:4700000,description:"Stations glow with aurora arcs and soft layered rings.",color:"#3affd0",accent:"#cc88ff",shape:"ring"},
  planet_sunset_worlds:{key:"planet_sunset_worlds",slot:"planet",name:"Sunset Planet Designs",price:4100000,description:"Planets gain warm sunset bands with orange-pink rings.",color:"#ff8844",accent:"#ff77dd",shape:"lush"},
  engine_prism_bloom:{key:"engine_prism_bloom",slot:"engine",name:"Prism Bloom Engines",price:6800000,description:"Multicolor engine bloom for premium ships.",color:"#ffffff",accent:"#ff5cff",rainbow:true,shape:"flare"},
  shield_nebula_shell:{key:"shield_nebula_shell",slot:"shield",name:"Nebula Shell Shield",price:5300000,description:"A layered violet nebula shell shield aura.",color:"#7a5cff",accent:"#ff77dd",shape:"ring"},
  suit_cobalt_marshal:{key:"suit_cobalt_marshal",slot:"suit",name:"Cobalt Marshal Suit",price:3300000,description:"A cobalt-blue planetside suit with bright command trim.",color:"#58a6ff",accent:"#fff0a8",shape:"suit"},
  laser_mining_rose:{key:"laser_mining_rose",slot:"laser",name:"Rose Mining Beam",price:3450000,description:"Pink rose-colored mining beam and highlight effects.",color:"#ff77dd",accent:"#fff0ff",shape:"beam"}
});


Object.assign(COSMETIC_DEFS,{
  ship_obsidian_moth:{key:"ship_obsidian_moth",slot:"ship",name:"Obsidian Moth Hull",price:8200000,description:"Black obsidian wings with violet miasma edge glow.",color:"#07070b",accent:"#9b42ff",shape:"stingray"},
  ship_codex_neon_viper:{key:"ship_codex_neon_viper",slot:"ship",name:"Codex Neon Viper Hull",price:9100000,description:"Cyan-gold viper frame with bright codex accents.",color:"#00f0ff",accent:"#ffdd44",shape:"lancer"},
  bullet_miasma_bubbles:{key:"bullet_miasma_bubbles",slot:"bullet",name:"Miasma Bubble Shots",price:4400000,description:"Purple miasma bubble projectiles.",color:"#9b42ff",accent:"#d45cff",sizeBoost:.9},
  bullet_obsidian_sparks:{key:"bullet_obsidian_sparks",slot:"bullet",name:"Obsidian Spark Shots",price:5100000,description:"Dark sparks with violet-white hot centers.",color:"#12051f",accent:"#ffffff",sizeBoost:.7},
  enemy_void_mimics:{key:"enemy_void_mimics",slot:"enemy",name:"Void Mimic Enemies",price:7200000,description:"Enemies appear as void-mimic silhouettes.",color:"#1a0d2e",accent:"#ff77dd",shape:"bat"},
  npcship_codex_merchants:{key:"npcship_codex_merchants",slot:"npcship",name:"Codex Merchant Ships",price:6600000,description:"NPC convoys use cyan-gold merchant hulls.",color:"#00f0ff",accent:"#ffdd44",shape:"hauler"},
  station_obsidian_gate:{key:"station_obsidian_gate",slot:"station",name:"Obsidian Gate Stations",price:7600000,description:"Stations turn into dark gate hubs with purple cores.",color:"#07070b",accent:"#9b42ff",shape:"spire"},
  planet_miasma_worlds:{key:"planet_miasma_worlds",slot:"planet",name:"Miasma Planet Designs",price:7500000,description:"Planet cosmetics with purple miasma oceans and black crust.",color:"#7324a8",accent:"#d45cff",shape:"void"},
  engine_void_pulse:{key:"engine_void_pulse",slot:"engine",name:"Void Pulse Engines",price:7200000,description:"Pulsing dark-violet engine core.",color:"#1a0d2e",accent:"#ff77dd",shape:"flare"},
  shield_charcoal_dome:{key:"shield_charcoal_dome",slot:"shield",name:"Charcoal Dome Shield",price:3900000,description:"Smoky charcoal shield aura.",color:"#25211f",accent:"#7c6a55",shape:"ring"},
  suit_codex_neon:{key:"suit_codex_neon",slot:"suit",name:"Codex Neon Suit",price:4800000,description:"Planetside suit with codex cyan and gold trim.",color:"#00f0ff",accent:"#ffdd44",shape:"suit"},
  laser_mining_obsidian:{key:"laser_mining_obsidian",slot:"laser",name:"Obsidian Mining Beam",price:5200000,description:"Dark mining beam with violet edge pulse.",color:"#07070b",accent:"#9b42ff",shape:"beam"}
});
Object.assign(COSMETIC_DEFS,{
  spliced_ship_01:{key:"spliced_ship_01",slot:"ship",name:"Spliced Ship Skin 01",price:1075000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_01.png",spriteScale:0.2},
  spliced_ship_02:{key:"spliced_ship_02",slot:"ship",name:"Spliced Ship Skin 02",price:1250000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_02.png",spriteScale:0.2},
  spliced_ship_03:{key:"spliced_ship_03",slot:"ship",name:"Spliced Ship Skin 03",price:1425000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_03.png",spriteScale:0.2},
  spliced_ship_04:{key:"spliced_ship_04",slot:"ship",name:"Spliced Ship Skin 04",price:1600000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_04.png",spriteScale:0.2},
  spliced_ship_05:{key:"spliced_ship_05",slot:"ship",name:"Spliced Ship Skin 05",price:1775000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_05.png",spriteScale:0.2},
  spliced_ship_06:{key:"spliced_ship_06",slot:"ship",name:"Spliced Ship Skin 06",price:1950000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_06.png",spriteScale:0.2},
  spliced_ship_07:{key:"spliced_ship_07",slot:"ship",name:"Spliced Ship Skin 07",price:2125000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_07.png",spriteScale:0.2},
  spliced_ship_08:{key:"spliced_ship_08",slot:"ship",name:"Spliced Ship Skin 08",price:2300000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_08.png",spriteScale:0.2},
  spliced_ship_09:{key:"spliced_ship_09",slot:"ship",name:"Spliced Ship Skin 09",price:2475000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_09.png",spriteScale:0.2},
  spliced_ship_10:{key:"spliced_ship_10",slot:"ship",name:"Spliced Ship Skin 10",price:2650000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_10.png",spriteScale:0.2},
  spliced_ship_11:{key:"spliced_ship_11",slot:"ship",name:"Spliced Ship Skin 11",price:2825000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_11.png",spriteScale:0.2},
  spliced_ship_12:{key:"spliced_ship_12",slot:"ship",name:"Spliced Ship Skin 12",price:3000000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_12.png",spriteScale:0.2},
  spliced_ship_13:{key:"spliced_ship_13",slot:"ship",name:"Spliced Ship Skin 13",price:3175000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_13.png",spriteScale:0.2},
  spliced_ship_14:{key:"spliced_ship_14",slot:"ship",name:"Spliced Ship Skin 14",price:3350000,description:"Imported ship sprite from the spliced sprite sheet for player ships.",color:"#7be6ff",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_14.png",spriteScale:0.2},
  spliced_npcship_01:{key:"spliced_npcship_01",slot:"npcship",name:"Spliced NPC Hull 01",price:1280000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_15.png",spriteScale:0.2},
  spliced_npcship_02:{key:"spliced_npcship_02",slot:"npcship",name:"Spliced NPC Hull 02",price:1460000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_16.png",spriteScale:0.2},
  spliced_npcship_03:{key:"spliced_npcship_03",slot:"npcship",name:"Spliced NPC Hull 03",price:1640000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_17.png",spriteScale:0.2},
  spliced_npcship_04:{key:"spliced_npcship_04",slot:"npcship",name:"Spliced NPC Hull 04",price:1820000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_18.png",spriteScale:0.2},
  spliced_npcship_05:{key:"spliced_npcship_05",slot:"npcship",name:"Spliced NPC Hull 05",price:2000000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_19.png",spriteScale:0.2},
  spliced_npcship_06:{key:"spliced_npcship_06",slot:"npcship",name:"Spliced NPC Hull 06",price:2180000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_20.png",spriteScale:0.2},
  spliced_npcship_07:{key:"spliced_npcship_07",slot:"npcship",name:"Spliced NPC Hull 07",price:2360000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_21.png",spriteScale:0.2},
  spliced_npcship_08:{key:"spliced_npcship_08",slot:"npcship",name:"Spliced NPC Hull 08",price:2540000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_22.png",spriteScale:0.2},
  spliced_npcship_09:{key:"spliced_npcship_09",slot:"npcship",name:"Spliced NPC Hull 09",price:2720000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_23.png",spriteScale:0.2},
  spliced_npcship_10:{key:"spliced_npcship_10",slot:"npcship",name:"Spliced NPC Hull 10",price:2900000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_24.png",spriteScale:0.2},
  spliced_npcship_11:{key:"spliced_npcship_11",slot:"npcship",name:"Spliced NPC Hull 11",price:3080000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_25.png",spriteScale:0.2},
  spliced_npcship_12:{key:"spliced_npcship_12",slot:"npcship",name:"Spliced NPC Hull 12",price:3260000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_26.png",spriteScale:0.2},
  spliced_npcship_13:{key:"spliced_npcship_13",slot:"npcship",name:"Spliced NPC Hull 13",price:3440000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_27.png",spriteScale:0.2},
  spliced_npcship_14:{key:"spliced_npcship_14",slot:"npcship",name:"Spliced NPC Hull 14",price:3620000,description:"Imported convoy/courier sprite from the spliced sprite sheet for NPC trade ships.",color:"#78ff8a",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_28.png",spriteScale:0.2},
  spliced_enemy_01:{key:"spliced_enemy_01",slot:"enemy",name:"Spliced Raider Skin 01",price:1545000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_29.png",spriteScale:0.19},
  spliced_enemy_02:{key:"spliced_enemy_02",slot:"enemy",name:"Spliced Raider Skin 02",price:1740000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_30.png",spriteScale:0.19},
  spliced_enemy_03:{key:"spliced_enemy_03",slot:"enemy",name:"Spliced Raider Skin 03",price:1935000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_31.png",spriteScale:0.19},
  spliced_enemy_04:{key:"spliced_enemy_04",slot:"enemy",name:"Spliced Raider Skin 04",price:2130000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_32.png",spriteScale:0.19},
  spliced_enemy_05:{key:"spliced_enemy_05",slot:"enemy",name:"Spliced Raider Skin 05",price:2325000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_33.png",spriteScale:0.19},
  spliced_enemy_06:{key:"spliced_enemy_06",slot:"enemy",name:"Spliced Raider Skin 06",price:2520000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_34.png",spriteScale:0.19},
  spliced_enemy_07:{key:"spliced_enemy_07",slot:"enemy",name:"Spliced Raider Skin 07",price:2715000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_35.png",spriteScale:0.19},
  spliced_enemy_08:{key:"spliced_enemy_08",slot:"enemy",name:"Spliced Raider Skin 08",price:2910000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_36.png",spriteScale:0.19},
  spliced_enemy_09:{key:"spliced_enemy_09",slot:"enemy",name:"Spliced Raider Skin 09",price:3105000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_37.png",spriteScale:0.19},
  spliced_enemy_10:{key:"spliced_enemy_10",slot:"enemy",name:"Spliced Raider Skin 10",price:3300000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_38.png",spriteScale:0.19},
  spliced_enemy_11:{key:"spliced_enemy_11",slot:"enemy",name:"Spliced Raider Skin 11",price:3495000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_39.png",spriteScale:0.19},
  spliced_enemy_12:{key:"spliced_enemy_12",slot:"enemy",name:"Spliced Raider Skin 12",price:3690000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_40.png",spriteScale:0.19},
  spliced_enemy_13:{key:"spliced_enemy_13",slot:"enemy",name:"Spliced Raider Skin 13",price:3885000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_41.png",spriteScale:0.19},
  spliced_enemy_14:{key:"spliced_enemy_14",slot:"enemy",name:"Spliced Raider Skin 14",price:4080000,description:"Imported raider sprite from the spliced sprite sheet for hostile enemy ships.",color:"#ff5544",accent:"#ffdd44",shape:"sprite",spritePath:"assets/spliced_ships/sprite_42.png",spriteScale:0.19},
});

const COUPON_DEFS = {
  SPACEECOISAWESOME:{credits:10000000,description:"Launch celebration coupon"},
  SEIA123:{credits:10000000,description:"Reusable Space Eco Infinite Awesome coupon",reusable:true}
};
Object.assign(COSMETIC_DEFS,{
  planet_sprite_01:{key:"planet_sprite_01",slot:"planet",name:"Ashen Iron Moon",price:1365000,description:"A cratered metallic moon for iron, titanium, and stone worlds. Resource planet: Metallic. Typical resources: Iron, Titanium, Stone.",color:"#b7844b",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_1.png",spriteScale:1.1,planetTypes:["metallic"],resourceKeys:["iron","titanium","stone"],resourcePlanetLabel:"Metallic"},
  planet_sprite_02:{key:"planet_sprite_02",slot:"planet",name:"Copper Crag World",price:1480000,description:"A brown mineral world for copper, charcoal, and dense soil deposits. Resource planet: Charcoal. Typical resources: Copper, Charcoal Block, Dirt.",color:"#428bba",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_2.png",spriteScale:1.1,planetTypes:["charcoal"],resourceKeys:["copper","charcoal_block","dirt"],resourcePlanetLabel:"Charcoal"},
  planet_sprite_03:{key:"planet_sprite_03",slot:"planet",name:"Astral Sand Moon",price:1595000,description:"A pale desert moon for sand, astral salt, and gold routes. Resource planet: Desert. Typical resources: Sand, Astral Salt, Gold.",color:"#8ab4d6",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_3.png",spriteScale:1.1,planetTypes:["desert"],resourceKeys:["sand","astral_salt","gold"],resourcePlanetLabel:"Desert"},
  planet_sprite_04:{key:"planet_sprite_04",slot:"planet",name:"Living Terra World",price:1710000,description:"A green-blue biosphere for dirt, grass, and crystal resources. Resource planet: Lush. Typical resources: Dirt, Grass Tuft, Crystal.",color:"#6c4a2b",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_4.png",spriteScale:1.1,planetTypes:["lush"],resourceKeys:["dirt","grass_tuft","crystal"],resourcePlanetLabel:"Lush"},
  planet_sprite_05:{key:"planet_sprite_05",slot:"planet",name:"Storm Ocean World",price:1825000,description:"A swirling ocean world for cobalt, ether glass, and ice deposits. Resource planet: Storm. Typical resources: Cobalt, Ether Glass, Ice Block.",color:"#477055",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_5.png",spriteScale:1.1,planetTypes:["storm"],resourceKeys:["cobalt","ether_glass","ice_block"],resourcePlanetLabel:"Storm"},
  planet_sprite_06:{key:"planet_sprite_06",slot:"planet",name:"Hex Ice World",price:1940000,description:"A frozen hex-shell world for ice block, black ice, and crystal. Resource planet: Ice. Typical resources: Ice Block, Black Ice, Crystal.",color:"#656566",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_6.png",spriteScale:1.1,planetTypes:["ice"],resourceKeys:["ice_block","black_ice","crystal"],resourcePlanetLabel:"Ice"},
  planet_sprite_07:{key:"planet_sprite_07",slot:"planet",name:"Magma Crust World",price:2055000,description:"A magma-cracked world for lava rock, magma core, and ember quartz. Resource planet: Volcanic. Typical resources: Lava Rock, Magma Core, Ember Quartz.",color:"#16756f",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_7.png",spriteScale:1.1,planetTypes:["volcanic"],resourceKeys:["lava_rock","magma_core","ember_quartz"],resourcePlanetLabel:"Volcanic"},
  planet_sprite_08:{key:"planet_sprite_08",slot:"planet",name:"Charcoal Rock World",price:2170000,description:"A dark rock world for obsidian, gloom steel, and charcoal. Resource planet: Obsidian. Typical resources: Dark Obsidian, Gloom Steel, Charcoal Block.",color:"#762f1e",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_8.png",spriteScale:1.1,planetTypes:["obsidian"],resourceKeys:["dark_obsidian","gloom_steel","charcoal_block"],resourcePlanetLabel:"Obsidian"},
  planet_sprite_09:{key:"planet_sprite_09",slot:"planet",name:"Ember Mars World",price:2285000,description:"An orange scorched world for ember quartz, copper, and magma resources. Resource planet: Ember Quartz World. Typical resources: Ember Quartz, Copper, Magma Core.",color:"#474747",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_9.png",spriteScale:1.1,planetTypes:["ember_quartz_world"],resourceKeys:["ember_quartz","copper","magma_core"],resourcePlanetLabel:"Ember Quartz World"},
  planet_sprite_10:{key:"planet_sprite_10",slot:"planet",name:"Teal Miasma World",price:2400000,description:"A strange teal miasma world for corrupted sludge and miasma materials. Resource planet: Miasma. Typical resources: Purple Miasma, Miasma Core, Toxic Sludge.",color:"#603c8e",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_10.png",spriteScale:1.1,planetTypes:["miasma"],resourceKeys:["purple_miasma","miasma_core","toxic_sludge"],resourcePlanetLabel:"Miasma"},
  planet_sprite_11:{key:"planet_sprite_11",slot:"planet",name:"Violet Void World",price:2515000,description:"A violet void world for void ore, dark matter shards, and purple miasma. Resource planet: Void Spawn. Typical resources: Void Ore, Dark Matter Shard, Purple Miasma.",color:"#936d26",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_11.png",spriteScale:1.1,planetTypes:["void_spawn"],resourceKeys:["void_ore","dark_matter_shard","purple_miasma"],resourcePlanetLabel:"Void Spawn"},
  planet_sprite_12:{key:"planet_sprite_12",slot:"planet",name:"Amber Gold World",price:2630000,description:"An amber crater world for gold, astral salt, and desert materials. Resource planet: Desert. Typical resources: Gold, Astral Salt, Sand.",color:"#ac541b",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_12.png",spriteScale:1.1,planetTypes:["desert"],resourceKeys:["gold","astral_salt","sand"],resourcePlanetLabel:"Desert"},
  planet_sprite_13:{key:"planet_sprite_13",slot:"planet",name:"Cobalt Ocean World",price:2745000,description:"A deep blue storm world for cobalt, plasma cells, and ether glass. Resource planet: Storm. Typical resources: Cobalt, Plasma Cell, Ether Glass.",color:"#b28a5b",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_13.png",spriteScale:1.1,planetTypes:["storm"],resourceKeys:["cobalt","plasma_cell","ether_glass"],resourcePlanetLabel:"Storm"},
  planet_sprite_14:{key:"planet_sprite_14",slot:"planet",name:"Toxic Crater World",price:2860000,description:"A toxic green crater world for sludge, miasma cores, and copper. Resource planet: Toxic. Typical resources: Toxic Sludge, Miasma Core, Copper.",color:"#0b516f",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_14.png",spriteScale:1.1,planetTypes:["toxic"],resourceKeys:["toxic_sludge","miasma_core","copper"],resourcePlanetLabel:"Toxic"},
  planet_sprite_15:{key:"planet_sprite_15",slot:"planet",name:"Crystal Aqua World",price:2975000,description:"A bright aqua crystal world for crystal, prism ore, and ether glass. Resource planet: Crystal Forest. Typical resources: Crystal, Prism Ore, Ether Glass.",color:"#54651b",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_15.png",spriteScale:1.1,planetTypes:["crystal_forest"],resourceKeys:["crystal","prism_ore","ether_glass"],resourcePlanetLabel:"Crystal Forest"},
  planet_sprite_16:{key:"planet_sprite_16",slot:"planet",name:"Codex Circuit World",price:3090000,description:"A black-orange machine world for neon ore, codex shards, and circuitry. Resource planet: Codex Neon. Typical resources: Neon Ore, Codex Shard, Circuit Board.",color:"#28779b",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_16.png",spriteScale:1.1,planetTypes:["codex_neon"],resourceKeys:["neon_ore","codex_shard","circuit_board"],resourcePlanetLabel:"Codex Neon"},
  planet_sprite_17:{key:"planet_sprite_17",slot:"planet",name:"Fuel-Banded Giant",price:3205000,description:"A tan banded giant associated with fuel, gas canisters, and titanium trade. Resource planet: Metallic. Typical resources: Fuel, Gas Canister, Titanium.",color:"#694828",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_17.png",spriteScale:1.1,planetTypes:["metallic"],resourceKeys:["fuel","gas_canister","titanium"],resourcePlanetLabel:"Metallic"},
  planet_sprite_18:{key:"planet_sprite_18",slot:"planet",name:"Ringed Desert World",price:3320000,description:"A ringed desert world for sand, astral salt, and gold. Resource planet: Desert. Typical resources: Sand, Astral Salt, Gold.",color:"#a98b62",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_18.png",spriteScale:1.1,planetTypes:["desert"],resourceKeys:["sand","astral_salt","gold"],resourcePlanetLabel:"Desert"},
  planet_sprite_19:{key:"planet_sprite_19",slot:"planet",name:"Ringed Void World",price:3435000,description:"A purple ringed void world for void ore and dark matter resources. Resource planet: Void Spawn. Typical resources: Void Ore, Purple Miasma, Dark Matter Shard.",color:"#186da7",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_19.png",spriteScale:1.1,planetTypes:["void_spawn"],resourceKeys:["void_ore","purple_miasma","dark_matter_shard"],resourcePlanetLabel:"Void Spawn"},
  planet_sprite_20:{key:"planet_sprite_20",slot:"planet",name:"Blue Gas World",price:3550000,description:"A blue gas giant for cobalt, silicon, and crystal trade routes. Resource planet: Storm. Typical resources: Cobalt, Silicon, Crystal.",color:"#26529b",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_20.png",spriteScale:1.1,planetTypes:["storm"],resourceKeys:["cobalt","silicon","crystal"],resourcePlanetLabel:"Storm"},
  planet_sprite_21:{key:"planet_sprite_21",slot:"planet",name:"Ember Stripe Giant",price:3665000,description:"A red-orange banded giant for magma, ember quartz, and lava rock. Resource planet: Volcanic. Typical resources: Magma Core, Ember Quartz, Lava Rock.",color:"#b45437",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_21.png",spriteScale:1.1,planetTypes:["volcanic"],resourceKeys:["magma_core","ember_quartz","lava_rock"],resourcePlanetLabel:"Volcanic"},
  planet_sprite_22:{key:"planet_sprite_22",slot:"planet",name:"Mint Ether World",price:3780000,description:"A mint energy world for neon ore, ether glass, and prism ore. Resource planet: Neon Reef. Typical resources: Neon Ore, Ether Glass, Prism Ore.",color:"#5d957c",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_22.png",spriteScale:1.1,planetTypes:["neon_reef"],resourceKeys:["neon_ore","ether_glass","prism_ore"],resourcePlanetLabel:"Neon Reef"},
  planet_sprite_23:{key:"planet_sprite_23",slot:"planet",name:"Golden Ring Core",price:3895000,description:"A golden ringed world for gold, plasma cells, and quantum cores. Resource planet: Codex Neon. Typical resources: Gold, Plasma Cell, Quantum Core.",color:"#c48626",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_23.png",spriteScale:1.1,planetTypes:["codex_neon"],resourceKeys:["gold","plasma_cell","quantum_core"],resourcePlanetLabel:"Codex Neon"},
  planet_sprite_24:{key:"planet_sprite_24",slot:"planet",name:"Glowing Blue World",price:4010000,description:"A glowing blue world for black ice, crystal, and cobalt. Resource planet: Black Ice World. Typical resources: Black Ice, Crystal, Cobalt.",color:"#653e91",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_24.png",spriteScale:1.1,planetTypes:["black_ice_world"],resourceKeys:["black_ice","crystal","cobalt"],resourcePlanetLabel:"Black Ice World"},
  planet_sprite_25:{key:"planet_sprite_25",slot:"planet",name:"Lime Bloom World",price:4125000,description:"A lime-green biosphere for grass, soil, and bio-fiber resources. Resource planet: Lush. Typical resources: Grass Tuft, Dirt, Nano Fiber.",color:"#3d7896",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_25.png",spriteScale:1.1,planetTypes:["lush"],resourceKeys:["grass_tuft","dirt","nano_fiber"],resourcePlanetLabel:"Lush"},
  planet_sprite_26:{key:"planet_sprite_26",slot:"planet",name:"Rose Miasma World",price:4240000,description:"A rose-colored miasma world for miasma cores and prism ore. Resource planet: Miasma. Typical resources: Purple Miasma, Miasma Core, Prism Ore.",color:"#688f3f",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_26.png",spriteScale:1.1,planetTypes:["miasma"],resourceKeys:["purple_miasma","miasma_core","prism_ore"],resourcePlanetLabel:"Miasma"},
  planet_sprite_27:{key:"planet_sprite_27",slot:"planet",name:"Violet Crack World",price:4355000,description:"A cracked violet world for void ore, dark obsidian, and dark matter. Resource planet: Void Spawn. Typical resources: Void Ore, Dark Obsidian, Dark Matter Shard.",color:"#994468",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_27.png",spriteScale:1.1,planetTypes:["void_spawn"],resourceKeys:["void_ore","dark_obsidian","dark_matter_shard"],resourcePlanetLabel:"Void Spawn"},
  planet_sprite_28:{key:"planet_sprite_28",slot:"planet",name:"Shadow Moon",price:4470000,description:"A shadowy moon for charcoal, dark obsidian, and black ice. Resource planet: Charcoal. Typical resources: Charcoal Block, Dark Obsidian, Black Ice.",color:"#502f79",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_28.png",spriteScale:1.1,planetTypes:["charcoal"],resourceKeys:["charcoal_block","dark_obsidian","black_ice"],resourcePlanetLabel:"Charcoal"},
  planet_sprite_29:{key:"planet_sprite_29",slot:"planet",name:"Ice Spike World",price:4585000,description:"A spiked ice-crystal world for crystal, black ice, and prism ore. Resource planet: Crystal Forest. Typical resources: Crystal, Black Ice, Prism Ore.",color:"#39456b",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_29.png",spriteScale:1.1,planetTypes:["crystal_forest"],resourceKeys:["crystal","black_ice","prism_ore"],resourcePlanetLabel:"Crystal Forest"},
  planet_sprite_30:{key:"planet_sprite_30",slot:"planet",name:"Obsidian Spike World",price:4700000,description:"A hostile spiked world for dark obsidian, gloom steel, and void ore. Resource planet: Obsidian. Typical resources: Dark Obsidian, Gloom Steel, Void Ore.",color:"#433635",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_30.png",spriteScale:1.1,planetTypes:["obsidian"],resourceKeys:["dark_obsidian","gloom_steel","void_ore"],resourcePlanetLabel:"Obsidian"},
  planet_sprite_31:{key:"planet_sprite_31",slot:"planet",name:"Silver Titanium Moon",price:4815000,description:"A silver moon for stone, iron, and titanium. Resource planet: Metallic. Typical resources: Stone, Iron, Titanium.",color:"#2f5b6f",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_31.png",spriteScale:1.1,planetTypes:["metallic"],resourceKeys:["stone","iron","titanium"],resourcePlanetLabel:"Metallic"},
  planet_sprite_32:{key:"planet_sprite_32",slot:"planet",name:"Plasma Cobalt World",price:4930000,description:"An electric cobalt world for plasma cells, cobalt, and ether glass. Resource planet: Storm. Typical resources: Plasma Cell, Cobalt, Ether Glass.",color:"#0c577b",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_32.png",spriteScale:1.1,planetTypes:["storm"],resourceKeys:["plasma_cell","cobalt","ether_glass"],resourcePlanetLabel:"Storm"},
  planet_sprite_33:{key:"planet_sprite_33",slot:"planet",name:"Green Reef World",price:5045000,description:"A green reef world for neon ore, plant matter, and nano fiber. Resource planet: Neon Reef. Typical resources: Neon Ore, Grass Tuft, Nano Fiber.",color:"#64738e",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_33.png",spriteScale:1.1,planetTypes:["neon_reef"],resourceKeys:["neon_ore","grass_tuft","nano_fiber"],resourcePlanetLabel:"Neon Reef"},
  planet_sprite_34:{key:"planet_sprite_34",slot:"planet",name:"Magenta Pulse World",price:5160000,description:"A pulsing magenta world for purple miasma, miasma cores, and dark matter. Resource planet: Miasma. Typical resources: Purple Miasma, Miasma Core, Dark Matter Shard.",color:"#537735",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_34.png",spriteScale:1.1,planetTypes:["miasma"],resourceKeys:["purple_miasma","miasma_core","dark_matter_shard"],resourcePlanetLabel:"Miasma"},
  planet_sprite_35:{key:"planet_sprite_35",slot:"planet",name:"Solar Core World",price:5275000,description:"A molten solar world for ember quartz, gold, and magma core. Resource planet: Ember Quartz World. Typical resources: Ember Quartz, Gold, Magma Core.",color:"#bf6912",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_35.png",spriteScale:1.1,planetTypes:["ember_quartz_world"],resourceKeys:["ember_quartz","gold","magma_core"],resourcePlanetLabel:"Ember Quartz World"},
  planet_sprite_36:{key:"planet_sprite_36",slot:"planet",name:"Tech Shell World",price:5390000,description:"A blue machine-shell world for gloom steel, alloy frames, and circuit boards. Resource planet: Gloom Steel World. Typical resources: Gloom Steel, Alloy Frame, Circuit Board.",color:"#7f2a61",accent:"#ffffff",spritePath:"assets/spliced_planets/whitey 2.png_auto_36.png",spriteScale:1.1,planetTypes:["gloom_steel_world"],resourceKeys:["gloom_steel","alloy_frame","circuit_board"],resourcePlanetLabel:"Gloom Steel World"},
  station_sprite_01:{key:"station_sprite_01",slot:"station",name:"Orbital Nexus",price:1620000,description:"Orbital Nexus imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#6b764c",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_1.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_02:{key:"station_sprite_02",slot:"station",name:"Solar Dock",price:1740000,description:"Solar Dock imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#593c39",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_2.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_03:{key:"station_sprite_03",slot:"station",name:"Golden Relay",price:1860000,description:"Golden Relay imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#576674",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_3.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_04:{key:"station_sprite_04",slot:"station",name:"Verdant Crosshub",price:1980000,description:"Verdant Crosshub imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#49637b",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_4.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_05:{key:"station_sprite_05",slot:"station",name:"Azure Solar Hub",price:2100000,description:"Azure Solar Hub imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#866738",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_5.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_06:{key:"station_sprite_06",slot:"station",name:"Crimson Bastion",price:2220000,description:"Crimson Bastion imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#736584",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_6.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_07:{key:"station_sprite_07",slot:"station",name:"Void Halo",price:2340000,description:"Void Halo imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#5b6a75",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_7.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_08:{key:"station_sprite_08",slot:"station",name:"Frontier Port",price:2460000,description:"Frontier Port imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#65513e",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_8.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_09:{key:"station_sprite_09",slot:"station",name:"Industrial Yard",price:2580000,description:"Industrial Yard imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#5a696e",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_9.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_10:{key:"station_sprite_10",slot:"station",name:"Blue Citadel",price:2700000,description:"Blue Citadel imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#695636",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_10.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_11:{key:"station_sprite_11",slot:"station",name:"Sky Spire",price:2820000,description:"Sky Spire imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#525f69",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_11.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_12:{key:"station_sprite_12",slot:"station",name:"Ore Foundry",price:2940000,description:"Ore Foundry imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#506370",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_12.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_13:{key:"station_sprite_13",slot:"station",name:"Forge Ring",price:3060000,description:"Forge Ring imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#655e52",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_13.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_14:{key:"station_sprite_14",slot:"station",name:"Verdant Cluster",price:3180000,description:"Verdant Cluster imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#56663d",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_14.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_15:{key:"station_sprite_15",slot:"station",name:"Trade Beacon",price:3300000,description:"Trade Beacon imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#58656e",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_15.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_16:{key:"station_sprite_16",slot:"station",name:"Deep Dish Array",price:3420000,description:"Deep Dish Array imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#674c7f",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_16.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_17:{key:"station_sprite_17",slot:"station",name:"Shield Sphere",price:3540000,description:"Shield Sphere imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#4f5f67",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_17.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_18:{key:"station_sprite_18",slot:"station",name:"Twin-Sail Orbiter",price:3660000,description:"Twin-Sail Orbiter imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#6b7474",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_18.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_19:{key:"station_sprite_19",slot:"station",name:"Violet Core Hub",price:3780000,description:"Violet Core Hub imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#616663",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_19.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_20:{key:"station_sprite_20",slot:"station",name:"Aegis Ring",price:3900000,description:"Aegis Ring imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#536772",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_20.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_21:{key:"station_sprite_21",slot:"station",name:"Triad Beacon",price:4020000,description:"Triad Beacon imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#515e62",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_21.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_22:{key:"station_sprite_22",slot:"station",name:"Bio Reactor",price:4140000,description:"Bio Reactor imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#674a35",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_22.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_23:{key:"station_sprite_23",slot:"station",name:"Refinery Campus",price:4260000,description:"Refinery Campus imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#685039",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_23.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_24:{key:"station_sprite_24",slot:"station",name:"Lava Furnace",price:4380000,description:"Lava Furnace imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#4f5352",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_24.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_25:{key:"station_sprite_25",slot:"station",name:"Pulse Anchor",price:4500000,description:"Pulse Anchor imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#565b5c",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_25.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_26:{key:"station_sprite_26",slot:"station",name:"Cargo Pad",price:4620000,description:"Cargo Pad imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#506546",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_26.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_27:{key:"station_sprite_27",slot:"station",name:"Freight Pad",price:4740000,description:"Freight Pad imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#69523d",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_27.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_28:{key:"station_sprite_28",slot:"station",name:"Survey Disc",price:4860000,description:"Survey Disc imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#5e594b",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_28.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_29:{key:"station_sprite_29",slot:"station",name:"Orbital Loop",price:4980000,description:"Orbital Loop imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#847868",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_29.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_30:{key:"station_sprite_30",slot:"station",name:"Centroid Ring",price:5100000,description:"Centroid Ring imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#717a7c",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_30.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_31:{key:"station_sprite_31",slot:"station",name:"Golden Braces Hub",price:5220000,description:"Golden Braces Hub imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#85735c",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_31.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_32:{key:"station_sprite_32",slot:"station",name:"Wheelworks Station",price:5340000,description:"Wheelworks Station imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#7c8589",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_32.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_33:{key:"station_sprite_33",slot:"station",name:"Spoke Relay",price:5460000,description:"Spoke Relay imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#808586",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_33.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_34:{key:"station_sprite_34",slot:"station",name:"Celestial Crown",price:5580000,description:"Celestial Crown imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#71797f",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_34.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_35:{key:"station_sprite_35",slot:"station",name:"Moon Dock",price:5700000,description:"Moon Dock imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#72776a",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_35.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_36:{key:"station_sprite_36",slot:"station",name:"Glass Dome Port",price:5820000,description:"Glass Dome Port imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#5a4d88",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_36.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_37:{key:"station_sprite_37",slot:"station",name:"Aether Pylon",price:5940000,description:"Aether Pylon imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#483c80",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_37.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_38:{key:"station_sprite_38",slot:"station",name:"Verdant Talon",price:6060000,description:"Verdant Talon imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#614479",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_38.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_39:{key:"station_sprite_39",slot:"station",name:"Crystal Obelisk",price:6180000,description:"Crystal Obelisk imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#46708a",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_39.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_40:{key:"station_sprite_40",slot:"station",name:"Blue Gate Hub",price:6300000,description:"Blue Gate Hub imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#306868",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_40.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_41:{key:"station_sprite_41",slot:"station",name:"Royal Violet Hub",price:6420000,description:"Royal Violet Hub imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#5a736f",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_41.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_42:{key:"station_sprite_42",slot:"station",name:"Teal Shrine",price:6540000,description:"Teal Shrine imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#5c6e2d",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_42.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_43:{key:"station_sprite_43",slot:"station",name:"War Red Bastion",price:6660000,description:"War Red Bastion imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#513c37",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_43.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_44:{key:"station_sprite_44",slot:"station",name:"Red Blockhold",price:6780000,description:"Red Blockhold imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#53413e",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_44.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_45:{key:"station_sprite_45",slot:"station",name:"Red Citadel",price:6900000,description:"Red Citadel imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#4e3633",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_45.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_46:{key:"station_sprite_46",slot:"station",name:"Red Core Disk",price:7020000,description:"Red Core Disk imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#4f423f",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_46.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_47:{key:"station_sprite_47",slot:"station",name:"Red Spear Relay",price:7140000,description:"Red Spear Relay imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#4d3531",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_47.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_48:{key:"station_sprite_48",slot:"station",name:"Red Foundry",price:7260000,description:"Red Foundry imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#4b3a37",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_48.png",spriteScale:1.0,stationAssignable:true},
  station_sprite_49:{key:"station_sprite_49",slot:"station",name:"Red Tower",price:7380000,description:"Red Tower imported station design. After purchase, assign it to Outpost, Standard, Advanced, Capital, Super Station, or Wandering Exchange from the tier dropdown.",color:"#514542",accent:"#ffffff",spritePath:"assets/spliced_stations/whitey.png_auto_49.png",spriteScale:1.0,stationAssignable:true}
});

Object.assign(COSMETIC_DEFS,{
  turret_sprite_01:{key:"turret_sprite_01",slot:"turret",name:"Frontier Turret Design 01",price:940000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#6f6255",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_1.png",spriteScale:1.0},
  turret_sprite_02:{key:"turret_sprite_02",slot:"turret",name:"Frontier Turret Design 02",price:1030000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#5e4181",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_2.png",spriteScale:1.0},
  turret_sprite_03:{key:"turret_sprite_03",slot:"turret",name:"Frontier Turret Design 03",price:1120000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#416471",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_3.png",spriteScale:1.0},
  turret_sprite_04:{key:"turret_sprite_04",slot:"turret",name:"Frontier Turret Design 04",price:1210000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#766a59",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_4.png",spriteScale:1.0},
  turret_sprite_05:{key:"turret_sprite_05",slot:"turret",name:"Frontier Turret Design 05",price:1300000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#65767f",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_5.png",spriteScale:1.0},
  turret_sprite_06:{key:"turret_sprite_06",slot:"turret",name:"Frontier Turret Design 06",price:1390000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#596252",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_6.png",spriteScale:1.0},
  turret_sprite_07:{key:"turret_sprite_07",slot:"turret",name:"Frontier Turret Design 07",price:1480000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#7c7b7d",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_7.png",spriteScale:1.0},
  turret_sprite_08:{key:"turret_sprite_08",slot:"turret",name:"Frontier Turret Design 08",price:1570000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#51616c",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_8.png",spriteScale:1.0},
  turret_sprite_09:{key:"turret_sprite_09",slot:"turret",name:"Frontier Turret Design 09",price:1660000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#61544e",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_9.png",spriteScale:1.0},
  turret_sprite_10:{key:"turret_sprite_10",slot:"turret",name:"Frontier Turret Design 10",price:1750000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#5e6954",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_10.png",spriteScale:1.0},
  turret_sprite_11:{key:"turret_sprite_11",slot:"turret",name:"Frontier Turret Design 11",price:1840000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#486471",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_11.png",spriteScale:1.0},
  turret_sprite_12:{key:"turret_sprite_12",slot:"turret",name:"Frontier Turret Design 12",price:1930000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#58436b",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_12.png",spriteScale:1.0},
  turret_sprite_13:{key:"turret_sprite_13",slot:"turret",name:"Frontier Turret Design 13",price:2020000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#604745",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_13.png",spriteScale:1.0},
  turret_sprite_14:{key:"turret_sprite_14",slot:"turret",name:"Frontier Turret Design 14",price:2110000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#6f726d",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_14.png",spriteScale:1.0},
  turret_sprite_15:{key:"turret_sprite_15",slot:"turret",name:"Frontier Turret Design 15",price:2200000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#5b7d8c",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_15.png",spriteScale:1.0},
  turret_sprite_16:{key:"turret_sprite_16",slot:"turret",name:"Frontier Turret Design 16",price:2290000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#4c7a95",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_16.png",spriteScale:1.0},
  turret_sprite_17:{key:"turret_sprite_17",slot:"turret",name:"Frontier Turret Design 17",price:2380000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#4b7b8f",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_17.png",spriteScale:1.0},
  turret_sprite_18:{key:"turret_sprite_18",slot:"turret",name:"Frontier Turret Design 18",price:2470000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#877372",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_18.png",spriteScale:1.0},
  turret_sprite_19:{key:"turret_sprite_19",slot:"turret",name:"Frontier Turret Design 19",price:2560000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#7c5c3a",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_19.png",spriteScale:1.0},
  turret_sprite_20:{key:"turret_sprite_20",slot:"turret",name:"Frontier Turret Design 20",price:2650000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#6c604c",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_20.png",spriteScale:1.0},
  turret_sprite_21:{key:"turret_sprite_21",slot:"turret",name:"Frontier Turret Design 21",price:2740000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#446c4c",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_21.png",spriteScale:1.0},
  turret_sprite_22:{key:"turret_sprite_22",slot:"turret",name:"Frontier Turret Design 22",price:2830000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#5e704e",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_22.png",spriteScale:1.0},
  turret_sprite_23:{key:"turret_sprite_23",slot:"turret",name:"Frontier Turret Design 23",price:2920000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#644185",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_23.png",spriteScale:1.0},
  turret_sprite_24:{key:"turret_sprite_24",slot:"turret",name:"Frontier Turret Design 24",price:3010000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#594544",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_24.png",spriteScale:1.0},
  turret_sprite_25:{key:"turret_sprite_25",slot:"turret",name:"Frontier Turret Design 25",price:3100000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#648074",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_25.png",spriteScale:1.0},
  turret_sprite_26:{key:"turret_sprite_26",slot:"turret",name:"Frontier Turret Design 26",price:3190000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#665376",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_26.png",spriteScale:1.0},
  turret_sprite_27:{key:"turret_sprite_27",slot:"turret",name:"Frontier Turret Design 27",price:3280000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#517b7e",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_27.png",spriteScale:1.0},
  turret_sprite_28:{key:"turret_sprite_28",slot:"turret",name:"Frontier Turret Design 28",price:3370000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#666054",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_28.png",spriteScale:1.0},
  turret_sprite_29:{key:"turret_sprite_29",slot:"turret",name:"Frontier Turret Design 29",price:3460000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#564748",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_29.png",spriteScale:1.0},
  turret_sprite_30:{key:"turret_sprite_30",slot:"turret",name:"Frontier Turret Design 30",price:3550000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#556447",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_30.png",spriteScale:1.0},
  turret_sprite_31:{key:"turret_sprite_31",slot:"turret",name:"Frontier Turret Design 31",price:3640000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#67504f",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_31.png",spriteScale:1.0},
  turret_sprite_32:{key:"turret_sprite_32",slot:"turret",name:"Frontier Turret Design 32",price:3730000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#48606d",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_32.png",spriteScale:1.0},
  turret_sprite_33:{key:"turret_sprite_33",slot:"turret",name:"Frontier Turret Design 33",price:3820000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#406f7f",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_33.png",spriteScale:1.0},
  turret_sprite_34:{key:"turret_sprite_34",slot:"turret",name:"Frontier Turret Design 34",price:3910000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#6d6146",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_34.png",spriteScale:1.0},
  turret_sprite_35:{key:"turret_sprite_35",slot:"turret",name:"Frontier Turret Design 35",price:4000000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#436575",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_35.png",spriteScale:1.0},
  turret_sprite_36:{key:"turret_sprite_36",slot:"turret",name:"Frontier Turret Design 36",price:4090000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#563b73",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_36.png",spriteScale:1.0},
  turret_sprite_37:{key:"turret_sprite_37",slot:"turret",name:"Frontier Turret Design 37",price:4180000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#6a655a",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_37.png",spriteScale:1.0},
  turret_sprite_38:{key:"turret_sprite_38",slot:"turret",name:"Frontier Turret Design 38",price:4270000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#557584",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_38.png",spriteScale:1.0},
  turret_sprite_39:{key:"turret_sprite_39",slot:"turret",name:"Frontier Turret Design 39",price:4360000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#775752",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_39.png",spriteScale:1.0},
  turret_sprite_40:{key:"turret_sprite_40",slot:"turret",name:"Frontier Turret Design 40",price:4450000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#626f6d",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_40.png",spriteScale:1.0},
  turret_sprite_41:{key:"turret_sprite_41",slot:"turret",name:"Frontier Turret Design 41",price:4540000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#5f6f55",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_41.png",spriteScale:1.0},
  turret_sprite_42:{key:"turret_sprite_42",slot:"turret",name:"Frontier Turret Design 42",price:4630000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#7a6d4a",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_42.png",spriteScale:1.0},
  turret_sprite_43:{key:"turret_sprite_43",slot:"turret",name:"Frontier Turret Design 43",price:4720000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#565858",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_43.png",spriteScale:1.0},
  turret_sprite_44:{key:"turret_sprite_44",slot:"turret",name:"Frontier Turret Design 44",price:4810000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#487790",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_44.png",spriteScale:1.0},
  turret_sprite_45:{key:"turret_sprite_45",slot:"turret",name:"Frontier Turret Design 45",price:4900000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#56686c",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_45.png",spriteScale:1.0},
  turret_sprite_46:{key:"turret_sprite_46",slot:"turret",name:"Frontier Turret Design 46",price:4990000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#657262",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_46.png",spriteScale:1.0},
  turret_sprite_47:{key:"turret_sprite_47",slot:"turret",name:"Frontier Turret Design 47",price:5080000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#565f5e",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_47.png",spriteScale:1.0},
  turret_sprite_48:{key:"turret_sprite_48",slot:"turret",name:"Frontier Turret Design 48",price:5170000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#655151",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_48.png",spriteScale:1.0},
  turret_sprite_49:{key:"turret_sprite_49",slot:"turret",name:"Frontier Turret Design 49",price:5260000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#74643f",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_49.png",spriteScale:1.0},
  turret_sprite_50:{key:"turret_sprite_50",slot:"turret",name:"Frontier Turret Design 50",price:5350000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#6e787e",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_50.png",spriteScale:1.0},
  turret_sprite_51:{key:"turret_sprite_51",slot:"turret",name:"Frontier Turret Design 51",price:5440000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#6b6550",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_51.png",spriteScale:1.0},
  turret_sprite_52:{key:"turret_sprite_52",slot:"turret",name:"Frontier Turret Design 52",price:5530000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#56673e",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_52.png",spriteScale:1.0},
  turret_sprite_53:{key:"turret_sprite_53",slot:"turret",name:"Frontier Turret Design 53",price:5620000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#477c90",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_53.png",spriteScale:1.0},
  turret_sprite_54:{key:"turret_sprite_54",slot:"turret",name:"Frontier Turret Design 54",price:5710000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#573d6f",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_54.png",spriteScale:1.0},
  turret_sprite_55:{key:"turret_sprite_55",slot:"turret",name:"Frontier Turret Design 55",price:5800000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#597c84",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_55.png",spriteScale:1.0},
  turret_sprite_56:{key:"turret_sprite_56",slot:"turret",name:"Frontier Turret Design 56",price:5890000,description:"Imported turret sprite cosmetic for player-built defense turrets and civilization-zone turrets owned by the player.",color:"#586364",accent:"#ffdd44",spritePath:"assets/spliced_turrets/ChatGPT Image Jul 22, 2026, 08_23_35 PM.png_auto_56.png",spriteScale:1.0}
});

const COSMETIC_SLOTS = ["ship","bullet","enemy","npcship","particle","trail","station","planet","turret","engine","shield","suit","laser"];
const WORLD_COSMETIC_SLOTS = ["npcship","enemy","station","planet"];
function applySharedWorldCosmeticSlot(slot,key){
  if(!WORLD_COSMETIC_SLOTS.includes(slot))return false;
  if(key){const def=COSMETIC_DEFS[key]; if(!def||def.slot!==slot)return false; GLOBAL_WORLD_COSMETICS[slot]=key;}
  else GLOBAL_WORLD_COSMETICS[slot]=null;
  return true;
}
let GLOBAL_WORLD_COSMETICS={npcship:null,enemy:null,station:null,planet:null};
const PLANET_VISUAL_TYPES=["lush","desert","ice","toxic","volcanic","void_spawn","codex_neon","crystal_forest","storm","metallic","obsidian","miasma","charcoal","neon_reef","black_ice_world","ember_quartz_world","prism_moon","gloom_steel_world"];
function normalizePlanetTypeCosmetics(raw){const out={};for(const type of PLANET_VISUAL_TYPES)out[type]=null;if(raw&&typeof raw==="object")for(const type of PLANET_VISUAL_TYPES){const key=String(raw[type]||"");const def=COSMETIC_DEFS[key];if(key&&def?.slot==="planet"&&(!Array.isArray(def.planetTypes)||!def.planetTypes.length||def.planetTypes.includes(type)))out[type]=key;}return out;}
let GLOBAL_PLANET_TYPE_COSMETICS=normalizePlanetTypeCosmetics({});
function planetTypeForCosmetic(def){const type=String(def?.planetTypes?.[0]||"lush");return PLANET_VISUAL_TYPES.includes(type)?type:"lush";}
function normalizeCosmeticInventory(raw){
  const out={};
  if(raw&&typeof raw==="object")for(const [k,v] of Object.entries(raw)){if(COSMETIC_DEFS[k]&&v===true)out[k]=true;}
  return out;
}
function normalizeEquippedCosmetics(raw){
  const out={ship:null,bullet:null,enemy:null,npcship:null,particle:null,trail:null,station:null,planet:null,turret:null,engine:null,shield:null,suit:null,laser:null};
  if(raw&&typeof raw==="object")for(const slot of COSMETIC_SLOTS){const key=String(raw[slot]||"");if(key&&COSMETIC_DEFS[key]?.slot===slot)out[slot]=key;}
  return out;
}

const STATION_VISUAL_TIERS=["outpost","standard","advanced","capital","super","wandering_exchange"];
function normalizeStationTierCosmetics(raw){const out={};for(const tier of STATION_VISUAL_TIERS)out[tier]=null;if(raw&&typeof raw==="object")for(const tier of STATION_VISUAL_TIERS){const key=String(raw[tier]||"");if(key&&COSMETIC_DEFS[key]?.slot==="station")out[tier]=key;}return out;}
function syncOwnedZoneCosmeticsForPlayer(p){if(!p)return false;let changed=false;for(const zone of civilizationZones.values()){if(zone.ownerId===p.id||(p.memberId&&zone.ownerMemberId===p.memberId)){zone.stationTierCosmetics={};zone.npcshipCosmeticKey=null;zone.turretCosmeticKey=null;changed=true;}}return changed;}

function normalizeStoryProgress(raw){const completed=Math.max(0,Math.min(8,Math.floor(Number(raw?.completed)||0)));return{completed,startedAt:Math.max(0,Math.floor(Number(raw?.startedAt)||Date.now())),updatedAt:Math.max(0,Math.floor(Number(raw?.updatedAt)||Date.now()))};}
function normalizeRedeemedCoupons(raw){
  const out={};
  if(raw&&typeof raw==="object")for(const [k,v] of Object.entries(raw)){const code=String(k||"").trim().toUpperCase();if(code&&v===true)out[code]=true;}
  return out;
}
function publicCosmeticState(p){
  return {defs:COSMETIC_DEFS,owned:normalizeCosmeticInventory(p?.cosmeticInventory||{}),equipped:normalizeEquippedCosmetics(p?.equippedCosmetics||{}),stationTierCosmetics:normalizeStationTierCosmetics(p?.stationTierCosmetics||{}),planetTypeCosmetics:normalizePlanetTypeCosmetics(p?.planetTypeCosmetics||{}),redeemedCoupons:normalizeRedeemedCoupons(p?.redeemedCoupons||{}),spriteCosmeticRegistryVersion:1};
}
function sendCosmeticState(socket,p,reason="sync"){
  socket.emit("cosmeticState",{...publicCosmeticState(p),credits:p?.credits||0,reason});
}

/* ── Planetside module frame + crafting ── */
const PLANET_MODULE_MAX_LEVEL=10;
const PLANET_MODULE_ORDER=["life_support","suit_plating","mining_array","jetpack_capacitor","weapon_amplifier","resource_magnet"];
const PLANET_MODULE_DEFS={
  life_support:{key:"life_support",name:"CO₂ Scrubber Core",color:"#7be6ff",description:"Expands oxygen reserves and slows CO₂ buildup.",baseCredits:900,materials:{oxygen_tank:2,cobalt:3,circuit_board:1},advanced:[{level:4,type:"ether_glass",qty:1},{level:7,type:"quantum_core",qty:1}]},
  suit_plating:{key:"suit_plating",name:"Vitality Weave",color:"#78ff8a",description:"Adds suit health and surface damage resistance.",baseCredits:1100,materials:{nano_fiber:4,titanium:3,alloy_frame:1},advanced:[{level:4,type:"gloom_steel",qty:1},{level:7,type:"dark_matter_shard",qty:1}]},
  mining_array:{key:"mining_array",name:"Excavation Matrix",color:"#ffdd44",description:"Shortens mining duration and improves mining power.",baseCredits:1000,materials:{iron:8,copper:6,circuit_board:2},advanced:[{level:4,type:"prism_ore",qty:2},{level:7,type:"quantum_core",qty:1}]},
  jetpack_capacitor:{key:"jetpack_capacitor",name:"Jetpack Capacitor",color:"#ff9b42",description:"Extends jetpack flight time and recharge.",baseCredits:1200,materials:{fuel:4,plasma_cell:2,nano_fiber:2},advanced:[{level:4,type:"alloy_frame",qty:1},{level:7,type:"quantum_core",qty:1}]},
  weapon_amplifier:{key:"weapon_amplifier",name:"Surface Weapon Amplifier",color:"#ff77dd",description:"Boosts planetside weapon damage and cooldown.",baseCredits:1350,materials:{weapon_array:1,copper:6,plasma_cell:2},advanced:[{level:4,type:"miasma_core",qty:1},{level:7,type:"dark_matter_shard",qty:1}]},
  resource_magnet:{key:"resource_magnet",name:"Resource Magnet",color:"#cc88ff",description:"Expands planetside pickup range.",baseCredits:950,materials:{cobalt:4,crystal:4,circuit_board:2},advanced:[{level:4,type:"ether_glass",qty:2},{level:7,type:"stardust",qty:2}]}
};
function defaultPlanetModules(){return Object.fromEntries(PLANET_MODULE_ORDER.map(k=>[k,0]));}
function normalizePlanetModules(raw){const out=defaultPlanetModules();if(raw&&typeof raw==="object")for(const k of PLANET_MODULE_ORDER)out[k]=Math.max(0,Math.min(PLANET_MODULE_MAX_LEVEL,Math.floor(Number(raw[k])||0)));return out;}
function planetModuleLevel(p,key){return Math.max(0,Math.min(PLANET_MODULE_MAX_LEVEL,Math.floor(Number(p?.planetModules?.[key])||0)));}
function planetModuleRecipe(key,currentLevel){const def=PLANET_MODULE_DEFS[key];currentLevel=Math.max(0,Math.floor(Number(currentLevel)||0));if(!def||currentLevel>=PLANET_MODULE_MAX_LEVEL)return null;const target=currentLevel+1,growth=Math.pow(1.48,currentLevel),recipe={credits:Math.round(def.baseCredits*Math.pow(1.58,currentLevel))};for(const[type,base]of Object.entries(def.materials||{}))recipe[type]=Math.max(1,Math.ceil(base*growth));for(const gate of def.advanced||[])if(target>=gate.level)recipe[gate.type]=(recipe[gate.type]||0)+Math.max(1,Math.ceil(gate.qty*Math.pow(1.38,target-gate.level)));return recipe;}
function planetModuleEffects(p){const l=k=>planetModuleLevel(p,k);return{oxygenMaxBonus:l("life_support")*25,oxygenDrainMult:Math.pow(.95,l("life_support")),suitHpBonus:l("suit_plating")*18,damageReduction:Math.min(.35,l("suit_plating")*.03),miningSpeedMult:Math.pow(.93,l("mining_array")),miningPowerBonus:l("mining_array")*4,jetpackMaxBonus:l("jetpack_capacitor")*16,weaponDamageMult:1+l("weapon_amplifier")*.09,weaponCooldownMult:Math.max(.70,1-l("weapon_amplifier")*.025),pickupRangeBonus:l("resource_magnet")*10};}
function refreshPlanetSuitStats(p){if(!p)return;const desired=p.mode==="planet"?planetModuleEffects(p).suitHpBonus:0,current=Math.max(0,Number(p._planetSuitBonus)||0),baseMax=Math.max(1,(Number(p.maxHp)||100)-current);p.maxHp=baseMax+desired;if(desired>current)p.hp=Math.min(p.maxHp,(Number(p.hp)||baseMax)+(desired-current));else p.hp=Math.min(p.maxHp,Number(p.hp)||p.maxHp);p._planetSuitBonus=desired;}
function planetDamageAfterModules(p,raw){return Math.max(1,Number(raw||0)*(1-planetModuleEffects(p).damageReduction));}
function publicPlanetModuleDefs(){const out={};for(const[k,d]of Object.entries(PLANET_MODULE_DEFS))out[k]={key:k,name:d.name,color:d.color,description:d.description};return out;}
function sendPlanetModuleState(socket,p){socket.emit("planetModuleState",{planetModules:normalizePlanetModules(p.planetModules||{}),moduleDefs:publicPlanetModuleDefs(),hp:p.hp,maxHp:p.maxHp});}

/* ── Player state ── */
const players = new Map();

// A short in-memory handoff keeps a pilot's live session intact across a
// transient Socket.IO reconnect.  Persistent accounts still save through Wix;
// this specifically protects the common guest/embed disconnect path without
// trusting a client-supplied player snapshot.
const transientReconnectSessions = new Map();
const TRANSIENT_RECONNECT_TTL_MS = 120000;

function normalizeReconnectToken(raw){
  const token=String(raw||"").trim();
  return /^[A-Za-z0-9_-]{24,128}$/.test(token)?token:"";
}
function expireTransientReconnectSessions(){
  const now=Date.now();
  for(const [token,entry] of transientReconnectSessions){
    if(entry&&entry.expiresAt>now)continue;
    transientReconnectSessions.delete(token);
    // A session that did not return during the recovery window is a real
    // disconnect.  Finish the small amount of volatile social cleanup that
    // was deliberately deferred while we kept its pilot state available.
    const p=entry?.player,oldId=String(entry?.oldId||p?.id||"");
    if(p?.partyId){
      const party=parties.get(p.partyId);
      if(party){
        party.members.delete(oldId);
        party.invites?.delete(oldId);
        if(party.members.size===0)parties.delete(party.id);
        else{
          if(party.leaderId===oldId)party.leaderId=[...party.members][0]||null;
          emitPartyState(party.id);
        }
      }
      p.partyId=null;
    }
    if(p?.factionId){const faction=factions.get(p.factionId);if(faction)emitFactionState(faction.id);}
  }
}
function rememberTransientReconnectSession(p,token){
  token=normalizeReconnectToken(token);if(!p||!token)return false;
  expireTransientReconnectSessions();
  transientReconnectSessions.set(token,{player:p,oldId:p.id,memberId:p.memberId?String(p.memberId):null,expiresAt:Date.now()+TRANSIENT_RECONNECT_TTL_MS});
  return true;
}
function takeTransientReconnectSession(token,auth){
  token=normalizeReconnectToken(token);if(!token)return null;
  expireTransientReconnectSessions();
  const entry=transientReconnectSessions.get(token);if(!entry)return null;
  // Never use a short-lived reconnect token to switch between member accounts.
  // A briefly expired Wix token is allowed to resume its own in-memory session;
  // the reconnect token itself is random and never accepted as a long-term login.
  if(entry.memberId&&auth?.memberId&&String(auth.memberId)!==entry.memberId)return null;
  transientReconnectSessions.delete(token);
  return entry;
}
function rebindTransientPlayerSession(p,oldId,newId,displayName){
  if(!p)return;
  p.id=newId;p.name=sanitizeName(displayName||p.name);p.lastSeen=Date.now();p.ping=0;p.pingTs=Date.now();
  // Never carry a held key across a transport replacement.
  p.input={rotLeft:false,rotRight:false,thrust:false,brake:false,shootX:null,shootY:null};
  for(const st of ownedStations.values())if(st.ownerId===oldId){st.ownerId=newId;st.ownerName=p.name;}
  for(const st of ownedStructures.values())if(st.ownerId===oldId){st.ownerId=newId;st.ownerName=p.name;}
  for(const zone of civilizationZones.values())if(zone.ownerId===oldId){zone.ownerId=newId;zone.ownerName=p.name;}
  if(p.partyId){const party=parties.get(p.partyId);if(party){party.members.delete(oldId);party.members.add(newId);if(party.leaderId===oldId)party.leaderId=newId;for(const [inviteId,invite] of party.invites){if(inviteId===oldId){party.invites.delete(inviteId);party.invites.set(newId,invite);}if(invite?.fromId===oldId)invite.fromId=newId;}}}
  if(p.factionId){const faction=factions.get(p.factionId);if(faction){faction.members.delete(oldId);faction.members.add(newId);if(faction.leaderId===oldId)faction.leaderId=newId;if(faction.memberMeta?.[oldId]){faction.memberMeta[newId]=faction.memberMeta[oldId];delete faction.memberMeta[oldId];}for(const [inviteId,invite] of faction.invites||[]){if(inviteId===oldId){faction.invites.delete(inviteId);faction.invites.set(newId,invite);}if(invite?.fromId===oldId)invite.fromId=newId;}}}
}
const transientReconnectSweepTimer=setInterval(expireTransientReconnectSessions,30000);
if(typeof transientReconnectSweepTimer.unref==="function")transientReconnectSweepTimer.unref();

function defaultPlayer(id, name, x, y) {
  return {
    id, name:sanitizeName(name), x, y,
    vx:0, vy:0, angle:0,
    hp:100, maxHp:100, shield:60, maxShield:60,
    level:1, xp:0, attrPoints:0,
    credits:300, maxSlots:24, invSlots:emptySlots(24), color:randomShipColor(), shipType:"scout",
    input:{ rotLeft:false, rotRight:false, thrust:false, brake:false, shootX:null, shootY:null },
    shootCooldown:0, lastSeen:Date.now(), mode:"space", planetId:null,
    attrs:{ damage:1, speed:1, cargoMax:1, armor:1, gasEfficiency:1, shieldRegen:1, braking:1 },
    energy:100, shieldRegenTimer:0,
    score:0, kills:0, deaths:0, tradingVolume:0, miningScore:0,
    ping:0, pingTs:0,
    planetX:0, planetY:0, planetVx:0, planetVy:0, planetTool:"mining",
    cosmeticColor:"#ffd27a", suitColor:"#ffffff", weaponLevel:1, miningLevel:1, oxygenLevel:1,
    badgeRewards:{},storyProgress:normalizeStoryProgress({}),
    cosmeticInventory:{}, equippedCosmetics:{ship:null,bullet:null,enemy:null,npcship:null,particle:null,trail:null,station:null,planet:null,turret:null,engine:null,shield:null,suit:null,laser:null}, stationTierCosmetics:normalizeStationTierCosmetics({}), planetTypeCosmetics:normalizePlanetTypeCosmetics({}), redeemedCoupons:{},
    equippedWeapon:"weapon_laser_mk1",weaponLevels:{weapon_laser_mk1:1},
    equippedAttachments:defaultAttachmentSlots(),
    planetModules:defaultPlanetModules(),
  };
}

function sanitizeName(raw) { return String(raw||"Pilot").replace(/[^a-zA-Z0-9_ \-]/g,"").slice(0,16).trim()||"Pilot"; }
function randomShipColor() { const p=["#7be6ff","#ff9944","#66ff88","#ff66aa","#ffdd44","#cc88ff","#44ccff","#ff6644"]; return p[Math.floor(Math.random()*p.length)]; }

function characterUpgradeCost(player,kind){
  const levels={weapon:player.weaponLevel||1,mining:player.miningLevel||1,oxygen:player.oxygenLevel||1};
  const base={weapon:750,mining:650,oxygen:500}[kind]||999999;
  return Math.floor(base*Math.pow(1.65,Math.max(0,(levels[kind]||1)-1)));
}
function planetWeaponDamage(player){return (12+((player.weaponLevel||1)-1)*5)*planetModuleEffects(player).weaponDamageMult;}
function sendCharacterState(socket,p){socket.emit("characterState",{cosmeticColor:p.cosmeticColor,suitColor:p.suitColor,weaponLevel:p.weaponLevel||1,miningLevel:p.miningLevel||1,oxygenLevel:p.oxygenLevel||1,credits:p.credits,planetModules:normalizePlanetModules(p.planetModules||{}),hp:p.hp,maxHp:p.maxHp});}

/* ── Score ── */
function addScore(player, amount, reason) {
  player.score = (player.score||0) + amount;
  io.to(player.id).emit("scoreUpdate", { score:player.score, delta:amount, reason });
}
function playerXpNeeded(level){return Math.floor(100*Math.pow(1.4,Math.max(1,level)-1));}
function addPlayerXpOnly(player,amount,reason="XP"){
  if(!player||amount<=0)return;
  amount=Math.max(0,Math.floor(Number(amount)||0));
  if(amount<=0)return;
  player.xp=(player.xp||0)+amount;
  player.miningScore=(player.miningScore||0)+amount;
  addScore(player,Math.floor(amount*0.5),reason);
  let leveled=false;
  while(player.xp>=playerXpNeeded(player.level)){
    player.xp-=playerXpNeeded(player.level);
    player.level++;
    player.attrPoints=(player.attrPoints||0)+2;
    leveled=true;
  }
  if(leveled)io.to(player.id).emit("levelUp",{level:player.level,attrPoints:player.attrPoints});
  io.to(player.id).emit("xpUpdate",{xp:player.xp,level:player.level});
  if(typeof persistPlayerSoon==="function")persistPlayerSoon(player,"gain_xp");
}
function grantXp(player,amount,reason="Mining/Combat"){
  if(!player||amount<=0)return;
  amount=Math.max(0,Math.floor(Number(amount)||0));
  addPlayerXpOnly(player,amount,reason);
  contributeFactionXp(player,amount,reason);
}

function buildLeaderboard(limit=10) {
  return [...players.values()]
    .sort((a,b) => (b.score||0)-(a.score||0))
    .slice(0, limit)
    .map((p,i) => ({ rank:i+1, id:p.id, name:p.name, score:p.score||0, kills:p.kills||0, deaths:p.deaths||0, level:p.level, credits:p.credits, x:Math.round(p.x), y:Math.round(p.y), shipType:p.shipType||"scout" }));
}

/* ── Spawn ── */
function computeSpawnPoint() {
  const active = [...players.values()].filter(p => Date.now()-p.lastSeen < 60000);
  if (active.length === 0) { const a=Math.random()*Math.PI*2,r=DEAD_ZONE+Math.random()*200; return { x:Math.cos(a)*r, y:Math.sin(a)*r }; }
  let cx=0,cy=0; for(const p of active){cx+=p.x;cy+=p.y;} cx/=active.length; cy/=active.length;
  const a=Math.random()*Math.PI*2, r=200+Math.random()*SPAWN_RADIUS;
  return { x:cx+Math.cos(a)*r, y:cy+Math.sin(a)*r };
}

/* ── Economy ── */
function xmur3(str){let h=1779033703^str.length;for(let i=0;i<str.length;i++){h=Math.imul(h^str.charCodeAt(i),3432918353);h=(h<<13)|(h>>>19);}return()=>{h=Math.imul(h^(h>>>16),2246822507);h=Math.imul(h^(h>>>13),3266489909);return((h^=h>>>16)>>>0);};}
function sfc32(a,b,c,d){return()=>{a|=0;b|=0;c|=0;d|=0;let t=(a+b|0)+d|0;d=d+1|0;a=b^b>>>9;b=c+(c<<3)|0;c=(c<<21|c>>>11);c=c+t|0;return(t>>>0)/4294967296;};}
function makeRng(s){const seed=xmur3(s);return sfc32(seed(),seed(),seed(),seed());}

const WEAPON_DEFS={
  weapon_laser_mk1:{key:"weapon_laser_mk1",name:"Pulse Laser",class:"Laser",rarity:3,color:"#ffff66",damage:18,cooldown:0.20,speed:320,life:2.1,shots:1,spread:0,size:2.7,mode:"single",upgradeMult:1.16},
  weapon_scatter_blaster:{key:"weapon_scatter_blaster",name:"Scatter Blaster",class:"Blaster",rarity:4,color:"#ff8844",damage:11,cooldown:0.34,speed:270,life:1.45,shots:5,spread:0.36,size:2.4,mode:"spread",upgradeMult:1.14},
  weapon_ion_lance:{key:"weapon_ion_lance",name:"Ion Lance",class:"Lance",rarity:5,color:"#7be6ff",damage:31,cooldown:0.42,speed:430,life:1.9,shots:1,spread:0,size:3.2,mode:"pierce",upgradeMult:1.18},
  weapon_plasma_orb:{key:"weapon_plasma_orb",name:"Plasma Orb",class:"Plasma",rarity:6,color:"#cc88ff",damage:44,cooldown:0.62,speed:220,life:2.6,shots:1,spread:0,size:5.5,mode:"orb",upgradeMult:1.20},
  weapon_rail_cannon:{key:"weapon_rail_cannon",name:"Rail Cannon",class:"Rail",rarity:7,color:"#d6e1ff",damage:68,cooldown:0.92,speed:620,life:1.25,shots:1,spread:0,size:2.2,mode:"rail",upgradeMult:1.22},
  weapon_meteor_swarm:{key:"weapon_meteor_swarm",name:"Meteor Swarm",class:"Swarm",rarity:8,color:"#ff5c7a",damage:16,cooldown:0.74,speed:285,life:2.25,shots:8,spread:0.75,size:3.1,mode:"swarm",upgradeMult:1.17}
};
const WEAPON_KEYS=Object.keys(WEAPON_DEFS);
Object.assign(WEAPON_DEFS,{
  weapon_arc_pulser:{key:"weapon_arc_pulser",name:"Arc Pulser",class:"Arc",rarity:5,color:"#62ffe0",damage:22,cooldown:0.27,speed:340,life:1.7,shots:3,spread:0.22,size:2.8,mode:"arc",upgradeMult:1.17,recipe:{credits:9500,copper:26,cobalt:16,circuit_board:6,plasma_cell:2}},
  weapon_frost_shard:{key:"weapon_frost_shard",name:"Frost Shard",class:"Shard",rarity:5,color:"#c8f6ff",damage:19,cooldown:0.36,speed:300,life:2.2,shots:4,spread:0.24,size:3.0,mode:"shard",upgradeMult:1.17,recipe:{credits:12000,ice_block:28,crystal:16,cobalt:10,nano_fiber:4}},
  weapon_sunflare_cannon:{key:"weapon_sunflare_cannon",name:"Sunflare Cannon",class:"Cannon",rarity:6,color:"#ffb347",damage:58,cooldown:0.78,speed:250,life:2.0,shots:1,spread:0,size:5.0,mode:"cannon",upgradeMult:1.20,recipe:{credits:18000,gold:28,magma_core:14,plasma_cell:8,alloy_frame:3}},
  weapon_graviton_burst:{key:"weapon_graviton_burst",name:"Graviton Burst",class:"Gravity",rarity:7,color:"#9b7bff",damage:33,cooldown:0.52,speed:260,life:2.4,shots:2,spread:0.1,size:4.5,mode:"gravity",upgradeMult:1.21,recipe:{credits:26000,crystal:30,dark_matter_shard:4,quantum_core:2,circuit_board:10}},
  weapon_bio_sprayer:{key:"weapon_bio_sprayer",name:"Bio Sprayer",class:"Sprayer",rarity:6,color:"#7eff7a",damage:13,cooldown:0.18,speed:230,life:1.35,shots:6,spread:0.52,size:2.7,mode:"spray",upgradeMult:1.16,recipe:{credits:15000,toxic_sludge:34,grass_tuft:20,nano_fiber:5,circuit_board:5}},
  weapon_void_spinner:{key:"weapon_void_spinner",name:"Void Spinner",class:"Void",rarity:8,color:"#ff77ff",damage:27,cooldown:0.46,speed:310,life:2.8,shots:5,spread:0.48,size:3.4,mode:"spinner",upgradeMult:1.22,recipe:{credits:38000,obelisk_core:1,dark_matter_shard:8,stardust:15,quantum_core:3,weapon_array:2}}
});
WEAPON_KEYS.push("weapon_arc_pulser","weapon_frost_shard","weapon_sunflare_cannon","weapon_graviton_burst","weapon_bio_sprayer","weapon_void_spinner");

/* ── Ship attachments / loadout ──
   Attachments are server-authoritative passive modules. They are equipped from
   inventory, not consumed, and they update the same combat stats used by PvP.
*/
const ATTACHMENT_DEFS={
  hull_plate:{key:"hull_plate",slot:"hull",name:"Reinforced Hull Plate",maxHpBonus:35,description:"Adds extra hull durability."},
  shield_matrix:{key:"shield_matrix",slot:"shield",name:"Shield Matrix",maxShieldBonus:32,shieldRegenMult:1.10,description:"Boosts shields and shield recovery."},
  engine_core:{key:"engine_core",slot:"engine",name:"Engine Core",thrustMult:1.10,description:"Improves ship thrust and handling."},
  nav_chip:{key:"nav_chip",slot:"utility",name:"Navigation Chip",gasEfficiencyMult:1.14,description:"Reduces travel energy drain."},
  cargo_pod:{key:"cargo_pod",slot:"utility",name:"Storage Pod",maxHpBonus:12,gasEfficiencyMult:1.06,description:"Balanced utility support module."},
  weapon_array:{key:"weapon_array",slot:"weapon",name:"Weapon Array",damageMult:1.12,description:"Amplifies ship weapon damage."},
  brake_servo:{key:"brake_servo",slot:"utility",name:"Brake Servo",brakingMult:1.32,description:"Increases braking response and drift control."},
  gyroscope_array:{key:"gyroscope_array",slot:"utility",name:"Gyroscope Array",turnMult:1.18,description:"Improves turn handling and rotational response."},
  overdrive_thruster:{key:"overdrive_thruster",slot:"engine",name:"Overdrive Thruster",thrustMult:1.22,turnMult:1.08,description:"Boosts speed and handling for agile ships."},
  combat_predictor:{key:"combat_predictor",slot:"weapon",name:"Combat Predictor",damageMult:1.18,turnMult:1.05,description:"Improves attack output and combat tracking."},
  shield_capacitor:{key:"shield_capacitor",slot:"shield",name:"Shield Capacitor",maxShieldBonus:55,description:"Adds a large shield capacity bonus."},
  regen_coil:{key:"regen_coil",slot:"shield",name:"Regen Coil",shieldRegenMult:1.34,description:"Improves shield recharge speed."},
  reinforced_bulkhead:{key:"reinforced_bulkhead",slot:"hull",name:"Reinforced Bulkhead",maxHpBonus:65,description:"Adds extra hull health for heavy builds."},
  maneuver_fins:{key:"maneuver_fins",slot:"utility",name:"Maneuver Fins",turnMult:1.28,brakingMult:1.12,description:"Improves turn handling and braking."}
};
const ATTACHMENT_SLOTS=["hull","shield","engine","utility","weapon"];
// Ship modules can now be manufactured from the loadout screen.  Crafted
// modules deliberately enter as their plain base item; upgrades/convergence
// create the individually keyed versions used by inventory, trade, and shops.
const MODULE_CRAFT_RECIPES={
  hull_plate:{credits:4200,iron:24,titanium:3},
  shield_matrix:{credits:6200,crystal:16,cobalt:8,circuit_board:3},
  engine_core:{credits:5900,copper:26,fuel:12,nano_fiber:3},
  nav_chip:{credits:7200,silicon:24,circuit_board:6,stardust:2},
  cargo_pod:{credits:4600,iron:18,copper:14,alloy_frame:2},
  weapon_array:{credits:8200,iron:22,plasma_cell:5,circuit_board:4},
  brake_servo:{credits:5600,cobalt:14,alloy_frame:3,fuel:7},
  gyroscope_array:{credits:7600,silicon:18,crystal:10,circuit_board:5},
  overdrive_thruster:{credits:12500,fuel:24,nano_fiber:8,engine_core:1},
  combat_predictor:{credits:14500,crystal:18,circuit_board:8,weapon_array:1},
  shield_capacitor:{credits:13200,crystal:22,cobalt:12,shield_matrix:1},
  regen_coil:{credits:11500,copper:20,crystal:16,plasma_cell:4},
  reinforced_bulkhead:{credits:15500,titanium:20,alloy_frame:7,hull_plate:1},
  maneuver_fins:{credits:7800,cobalt:16,nano_fiber:5,brake_servo:1}
};
function isAttachmentKey(k){return !!ATTACHMENT_DEFS[inventoryBaseType(k)];}
function defaultAttachmentSlots(){return {hull:null,shield:null,engine:null,utility:null,weapon:null};}
function normalizeAttachments(raw={}){
  const out=defaultAttachmentSlots();
  if(raw&&typeof raw==="object"){
    for(const slot of ATTACHMENT_SLOTS){
      const key=String(raw[slot]||"");
      if(key&&ATTACHMENT_DEFS[inventoryBaseType(key)]?.slot===slot)out[slot]=key;
    }
  }
  return out;
}
function attachmentEffectsFor(p){
  const fx={maxHpBonus:0,maxShieldBonus:0,thrustMult:1,damageMult:1,shieldRegenMult:1,gasEfficiencyMult:1,brakingMult:1,turnMult:1};
  const loadout=normalizeAttachments(p?.equippedAttachments||{});
  for(const key of Object.values(loadout)){
    const meta=moduleInstanceMeta(key),d=ATTACHMENT_DEFS[inventoryBaseType(key)];if(!d)continue;
    const lv=meta?.level||0,boost=1+lv*.055,bonus=String(meta?.bonus||"none");
    fx.maxHpBonus+=(Number(d.maxHpBonus)||0)*boost;
    fx.maxShieldBonus+=(Number(d.maxShieldBonus)||0)*boost;
    fx.thrustMult*=1+((Number(d.thrustMult)||1)-1)*boost;
    fx.damageMult*=1+((Number(d.damageMult)||1)-1)*boost;
    fx.shieldRegenMult*=1+((Number(d.shieldRegenMult)||1)-1)*boost;
    fx.gasEfficiencyMult*=1+((Number(d.gasEfficiencyMult)||1)-1)*boost;if(d.brakingMult)fx.brakingMult*=1+((Number(d.brakingMult)||1)-1)*boost;if(d.turnMult)fx.turnMult*=1+((Number(d.turnMult)||1)-1)*boost;
    if(bonus.includes("hull"))fx.maxHpBonus+=8+lv*2;if(bonus.includes("shield"))fx.maxShieldBonus+=8+lv*2;if(bonus.includes("damage"))fx.damageMult*=1.03+lv*.006;if(bonus.includes("thrust"))fx.thrustMult*=1.025+lv*.005;
  }
  return fx;
}
function finiteOrFallback(value,fallback){
  const n=Number(value);
  return Number.isFinite(n)?n:fallback;
}
function applyShipStats(p,refill=false){
  if(!p)return attachmentEffectsFor(p);
  p.equippedAttachments=normalizeAttachments(p.equippedAttachments||{});
  const def=SHIP_TYPES[p.shipType]||SHIP_TYPES.scout,fx=attachmentEffectsFor(p);
  const planetSuitBonus=p.mode==="planet"?planetModuleEffects(p).suitHpBonus:0;
  p.maxHp=Math.max(1,Math.floor((def.maxHp||100)+fx.maxHpBonus+planetSuitBonus));
  p._planetSuitBonus=planetSuitBonus;
  p.maxShield=Math.max(0,Math.floor((def.maxShield||60)+fx.maxShieldBonus));
  if(refill){p.hp=p.maxHp;p.shield=p.maxShield;}
  else{
    // Preserve valid 0 values. The old `Number(value) || max` pattern treated a depleted
    // shield as missing data and could snap it back to full during sustained attacks.
    p.hp=Math.max(0,Math.min(finiteOrFallback(p.hp,p.maxHp),p.maxHp));
    p.shield=Math.max(0,Math.min(finiteOrFallback(p.shield,p.maxShield),p.maxShield));
  }
  return fx;
}
const RES_KEYS=["dirt","stone","copper","iron","gold","crystal","fuel","gas_canister","oxygen_tank","ice_block","lava_rock","magma_core","toxic_sludge","sand","grass_tuft","hull_plate","engine_core","shield_matrix","weapon_array","cargo_pod","nav_chip","obelisk_core",...WEAPON_KEYS];
const RES_BASE={dirt:1,stone:3,copper:9,iron:10,gold:40,crystal:60,fuel:25,gas_canister:30,oxygen_tank:35,ice_block:4,lava_rock:12,magma_core:22,toxic_sludge:8,sand:2,grass_tuft:1,hull_plate:85,engine_core:140,shield_matrix:170,weapon_array:190,cargo_pod:95,nav_chip:155,obelisk_core:800,weapon_laser_mk1:260,weapon_scatter_blaster:520,weapon_ion_lance:900,weapon_plasma_orb:1450,weapon_rail_cannon:2400,weapon_meteor_swarm:4200};
const RES_RARITY={dirt:1,stone:2,copper:3,iron:3,gold:5,crystal:6,fuel:4,gas_canister:2,oxygen_tank:2,ice_block:2,lava_rock:3,magma_core:4,toxic_sludge:3,sand:1,grass_tuft:1,hull_plate:5,engine_core:6,shield_matrix:6,weapon_array:6,cargo_pod:5,nav_chip:6,obelisk_core:8,weapon_laser_mk1:3,weapon_scatter_blaster:4,weapon_ion_lance:5,weapon_plasma_orb:6,weapon_rail_cannon:7,weapon_meteor_swarm:8};
Object.assign(RES_BASE,{brake_servo:115,gyroscope_array:150,overdrive_thruster:220,combat_predictor:240,shield_capacitor:185,regen_coil:165,reinforced_bulkhead:175,maneuver_fins:130,titanium:70,cobalt:55,silicon:18,nano_fiber:95,circuit_board:80,plasma_cell:120,dark_matter_shard:260,stardust:145,alloy_frame:180,quantum_core:320,weapon_arc_pulser:1150,weapon_frost_shard:1280,weapon_sunflare_cannon:2100,weapon_graviton_burst:3200,weapon_bio_sprayer:1850,weapon_void_spinner:5200});
Object.assign(RES_RARITY,{brake_servo:4,gyroscope_array:5,overdrive_thruster:6,combat_predictor:6,shield_capacitor:5,regen_coil:5,reinforced_bulkhead:5,maneuver_fins:4,titanium:5,cobalt:4,silicon:3,nano_fiber:5,circuit_board:4,plasma_cell:5,dark_matter_shard:7,stardust:6,alloy_frame:6,quantum_core:7,weapon_arc_pulser:5,weapon_frost_shard:5,weapon_sunflare_cannon:6,weapon_graviton_burst:7,weapon_bio_sprayer:6,weapon_void_spinner:8});
RES_KEYS.push("brake_servo","gyroscope_array","overdrive_thruster","combat_predictor","shield_capacitor","regen_coil","reinforced_bulkhead","maneuver_fins","titanium","cobalt","silicon","nano_fiber","circuit_board","plasma_cell","dark_matter_shard","stardust","alloy_frame","quantum_core","weapon_arc_pulser","weapon_frost_shard","weapon_sunflare_cannon","weapon_graviton_burst","weapon_bio_sprayer","weapon_void_spinner");


const SERVER_EXTRA_RESOURCE_DEFS={
  dark_obsidian:{base:210,rarity:6},purple_miasma:{base:145,rarity:5},charcoal_block:{base:12,rarity:2},neon_ore:{base:160,rarity:5},void_ore:{base:310,rarity:7},prism_ore:{base:230,rarity:6},astral_salt:{base:72,rarity:4},ether_glass:{base:205,rarity:6},codex_shard:{base:360,rarity:7},miasma_core:{base:520,rarity:8},black_ice:{base:130,rarity:5},ember_quartz:{base:150,rarity:5},gloom_steel:{base:240,rarity:6}
};
const SERVER_PROC_RESOURCE_KEYS=[];
const CLIENT_PROC_RESOURCE_KEYS=[];
const SERVER_RESOURCE_PUBLIC_DEFS={};
const SERVER_EXTRA_RESOURCE_PUBLIC_DEFS={
  dark_obsidian:{name:"Dark Obsidian",rarity:6,color:"#07070b",base:210,description:"Glass-black volcanic stone used in heavy hulls and void quests."},
  purple_miasma:{name:"Purple Miasma",rarity:5,color:"#9b42ff",base:145,description:"Violet vapor-block mineral used for exotic reactors and miasma contracts."},
  charcoal_block:{name:"Charcoal Block",rarity:2,color:"#25211f",base:12,description:"Compressed carbon block for early crafting, smelting, and station orders."},
  neon_ore:{name:"Neon Ore",rarity:5,color:"#00f0ff",base:160,description:"Bright codex-neon ore used in circuitry, signs, and energy tools."},
  void_ore:{name:"Void Ore",rarity:7,color:"#1a0d2e",base:310,description:"Dense shadow ore used for void weapons and high-value trade."},
  prism_ore:{name:"Prism Ore",rarity:6,color:"#ffd6ff",base:230,description:"Prismatic ore for shield crafting and luxury station work orders."},
  astral_salt:{name:"Astral Salt",rarity:4,color:"#fff4d6",base:72,description:"Glittering salt crystal used in trade quests and refinement."},
  ether_glass:{name:"Ether Glass",rarity:6,color:"#b8fff3",base:205,description:"Translucent glass resource for sensor optics and agile ship parts."},
  codex_shard:{name:"Codex Shard",rarity:7,color:"#ffdd44",base:360,description:"Rare golden-cyan data crystal used in codex-neon crafting."},
  miasma_core:{name:"Miasma Core",rarity:8,color:"#c13bff",base:520,description:"Condensed miasma heart for dangerous late-game recipes and contracts."},
  black_ice:{name:"Black Ice",rarity:5,color:"#1b2738",base:130,description:"Frozen shadow crystal from dark ice worlds."},
  ember_quartz:{name:"Ember Quartz",rarity:5,color:"#ff6b35",base:150,description:"Fiery quartz used in cannons, reactors, and forge quests."},
  gloom_steel:{name:"Gloom Steel",rarity:6,color:"#384052",base:240,description:"Heavy twilight alloy for hulls, brake assemblies, and defense orders."}
};
function procKeyTitle(key){return String(key||"").split("_").slice(2).map(v=>v?v[0].toUpperCase()+v.slice(1):"").join(" ")||"Procedural Resource";}
function registerServerGeneratedResources(){
  // Preserve the original server-only procedural keys for backwards-compatible saves.
  const prefixes=["astra","void","neon","miasma","codex","prism","ember","gloom","ether","nova","quantum","obsidian"],suffixes=["ore","shard","bloom","crystal","core","salt","glass","fiber","pearl","coal","spore","alloy"];
  const rng=makeRng(GALAXY_SEED+"|finite-proc-resources-v409");
  for(let i=0;i<28;i++){
    const key=`proc_${i}_${prefixes[i%prefixes.length]}_${suffixes[Math.floor(rng()*suffixes.length)]}`.replace(/[^a-z0-9_]/g,"_");
    const rarity=3+Math.floor(rng()*6),base=28+rarity*24+Math.floor(rng()*90);
    RES_BASE[key]=base;RES_RARITY[key]=rarity;
    if(!SERVER_PROC_RESOURCE_KEYS.includes(key))SERVER_PROC_RESOURCE_KEYS.push(key);
    SERVER_RESOURCE_PUBLIC_DEFS[key]={name:procKeyTitle(key),rarity,color:"#b58cff",base,generated:true,legacyServer:true,description:"Legacy procedural resource retained for saved inventories and trading compatibility."};
  }
}
function registerClientGeneratedResources(){
  // This is the exact browser generator. Previous builds used a different RNG draw
  // sequence on the server, so most client shop keys were rejected as “Unknown item”.
  const prefixes=["Astra","Void","Neon","Miasma","Codex","Prism","Ember","Gloom","Ether","Nova","Quantum","Obsidian"];
  const suffixes=["Ore","Shard","Bloom","Crystal","Core","Salt","Glass","Fiber","Pearl","Coal","Spore","Alloy"];
  const statKeys=["attack","damage","shield","regen","speed","braking","handling","craft","trade","quest","energy","armor"];
  const rng=makeRng(GALAXY_SEED+"|finite-proc-resources-v409");
  for(let i=0;i<28;i++){
    const key=`proc_${i}_${prefixes[i%prefixes.length].toLowerCase()}_${suffixes[Math.floor(rng()*suffixes.length)].toLowerCase()}`.replace(/[^a-z0-9_]/g,"_");
    const hue=Math.floor(rng()*360),rarity=3+Math.floor(rng()*6),base=28+rarity*24+Math.floor(rng()*90);
    const stats={};stats[statKeys[Math.floor(rng()*statKeys.length)]]=1+Math.floor(rng()*4);stats[statKeys[Math.floor(rng()*statKeys.length)]]=1+Math.floor(rng()*3);
    const name=`${prefixes[Math.floor(rng()*prefixes.length)]} ${suffixes[Math.floor(rng()*suffixes.length)]}`;
    // Browser-generated definitions are canonical for station stock. Override the
    // three overlapping legacy keys so display, price and rarity remain identical.
    RES_BASE[key]=base;RES_RARITY[key]=rarity;
    if(!CLIENT_PROC_RESOURCE_KEYS.includes(key))CLIENT_PROC_RESOURCE_KEYS.push(key);
    SERVER_RESOURCE_PUBLIC_DEFS[key]={name,rarity,color:`hsl(${hue},88%,62%)`,base,stats,generated:true,description:`Procedural ${name.toLowerCase()} used for station contracts, trading, and advanced crafting formulas.`};
  }
}
Object.assign(RES_BASE,Object.fromEntries(Object.entries(SERVER_EXTRA_RESOURCE_DEFS).map(([k,v])=>[k,v.base])));
Object.assign(RES_RARITY,Object.fromEntries(Object.entries(SERVER_EXTRA_RESOURCE_DEFS).map(([k,v])=>[k,v.rarity])));
RES_KEYS.push(...Object.keys(SERVER_EXTRA_RESOURCE_DEFS));
registerServerGeneratedResources();
registerClientGeneratedResources();
for(const key of [...SERVER_PROC_RESOURCE_KEYS,...CLIENT_PROC_RESOURCE_KEYS])if(!RES_KEYS.includes(key))RES_KEYS.push(key);
Object.assign(SERVER_RESOURCE_PUBLIC_DEFS,SERVER_EXTRA_RESOURCE_PUBLIC_DEFS);
const SHOP_RESOURCE_KEYS=[...Object.keys(SERVER_EXTRA_RESOURCE_DEFS),...CLIENT_PROC_RESOURCE_KEYS];
const RES_KEY_SET=new Set(RES_KEYS);
// A module instance is intentionally encoded in its item key.  Equal base,
// upgrade level and convergence bonuses yield the same key and can stack;
// every other combination remains a separate inventory stack without needing
// a second inventory table or weakening server authority during trades.
const MODULE_INSTANCE_PREFIX="mod__";
const MODULE_CONVERGENCE_BONUSES=["hull","shield","damage","thrust"];
function normalizeModuleBonuses(raw){
  const list=String(raw||"none").split("_").map(v=>v.trim().toLowerCase()).filter(v=>MODULE_CONVERGENCE_BONUSES.includes(v));
  return [...new Set(list)].sort();
}
function moduleInstanceMeta(key){
  key=String(key||"");if(!key.startsWith(MODULE_INSTANCE_PREFIX))return null;
  const parts=key.split("__");if(parts.length<4)return null;
  const base=String(parts[1]||""),level=Math.max(1,Math.min(10,Math.floor(Number(parts[2])||1))),rawBonus=String(parts.slice(3).join("__")||"none"),bonuses=normalizeModuleBonuses(rawBonus);
  if(!ATTACHMENT_DEFS[base])return null;
  // Reject forged metadata rather than silently converting it to a valid item.
  if((rawBonus!=="none"&&bonuses.join("_")!==rawBonus)||bonuses.length>MODULE_CONVERGENCE_BONUSES.length)return null;
  return {base,level,bonus:bonuses.length?bonuses.join("_"):"none",bonuses};
}
function moduleInstanceKey(base,level,bonus="none"){const bonuses=normalizeModuleBonuses(bonus);return `${MODULE_INSTANCE_PREFIX}${base}__${Math.max(1,Math.min(10,Math.floor(level||1)))}__${bonuses.length?bonuses.join("_"):"none"}`;}
function moduleTierForKey(key){const meta=moduleInstanceMeta(key);return {base:meta?.base||String(key||""),level:meta?.level||0,bonus:meta?.bonus||"none",bonuses:meta?.bonuses||[]};}
function moduleUpgradeCostFor(key){const m=moduleTierForKey(key),d=ATTACHMENT_DEFS[m.base]||{},statWeight=[d.maxHpBonus,d.maxShieldBonus,d.thrustMult&&d.thrustMult!==1,d.damageMult&&d.damageMult!==1,d.shieldRegenMult&&d.shieldRegenMult!==1,d.gasEfficiencyMult&&d.gasEfficiencyMult!==1,d.brakingMult&&d.brakingMult!==1,d.turnMult&&d.turnMult!==1].filter(Boolean).length||1,next=Math.min(10,m.level+1);return {credits:Math.floor((1800+statWeight*1100)*Math.pow(1.58,next-1)),resource:next<4?"iron":next<7?"crystal":"quantum_core",amount:Math.max(1,Math.ceil(next/3))};}
function moduleConvergenceCostFor(key,copies){const m=moduleTierForKey(key),base=moduleUpgradeCostFor(key);return {credits:Math.floor(base.credits*(1.25+Math.max(0,copies-1)*.12+m.bonuses.length*.35)),resource:m.level<5?"dark_matter_shard":"obelisk_core",amount:Math.max(1,Math.ceil((m.level+1+m.bonuses.length)/3))};}
function inventoryBaseType(key){return moduleInstanceMeta(key)?.base||String(key||"");}
function isInventoryItemKey(key){return RES_KEY_SET.has(String(key||""))||!!moduleInstanceMeta(key);}
function isKnownResourceKey(key){return isInventoryItemKey(key);}

const econRng=makeRng(GALAXY_SEED+"|economy");
const economy={
  drift:Object.fromEntries(RES_KEYS.map(k=>[k,1])),
  scarcity:Object.fromEntries(RES_KEYS.map(k=>[k,1])),
  tick(){for(const k of RES_KEYS){this.drift[k]=Math.max(0.6,Math.min(1.6,this.drift[k]+(econRng()-0.5)*0.02));this.scarcity[k]+=(1-this.scarcity[k])*0.002;}},
  price(k){const base=inventoryBaseType(k),meta=moduleInstanceMeta(k),b=(RES_BASE[base]||1)*(meta?(1+meta.level*.34+(meta.bonuses?.length||0)*.28):1),r=RES_RARITY[base]||1,f=1+(r-1)*0.28;return Math.max(1,Math.round(b*f*(this.drift[base]||1)*(this.scarcity[base]||1)));},
  sold(k,q){k=inventoryBaseType(k);this.scarcity[k]=Math.max(0.5,Math.min(1.5,(this.scarcity[k]||1)-q*0.02));},
  bought(k,q){k=inventoryBaseType(k);this.scarcity[k]=Math.max(0.5,Math.min(1.5,(this.scarcity[k]||1)+q*0.02));},
  snapshot(){const o={};for(const k of RES_KEYS)o[k]=this.price(k);return o;}
};
function isWeaponKey(k){return !!WEAPON_DEFS[k];}
function weaponLevelFor(p,k){return Math.max(1,Math.floor(p?.weaponLevels?.[k]||1));}
function weaponUpgradeCost(p,k){const d=WEAPON_DEFS[k];if(!d)return Infinity;const lvl=weaponLevelFor(p,k);return Math.ceil((economy.price(k)||d.damage*20)*(0.65+lvl*0.85)*Math.pow(1.42,lvl-1));}
function playerOwnsWeaponForEquip(p,key){return key==="weapon_laser_mk1"||inventoryCount(p,key)>0;}
function equippedWeaponKeyFor(p){return (p?.equippedWeapon&&isWeaponKey(p.equippedWeapon)&&playerOwnsWeaponForEquip(p,p.equippedWeapon))?p.equippedWeapon:"weapon_laser_mk1";}
function spawnWeaponProjectiles(p,ang,dmgStat){
  const key=equippedWeaponKeyFor(p),d=WEAPON_DEFS[key]||WEAPON_DEFS.weapon_laser_mk1,lvl=weaponLevelFor(p,key),shots=d.shots||1,spread=d.spread||0;
  const totalDamage=d.damage*Math.pow(d.upgradeMult||1.15,lvl-1)*dmgStat;
  const spawned=[];
  for(let i=0;i<shots;i++){
    const offset=shots===1?0:(i-(shots-1)/2)*(spread/Math.max(1,shots-1));
    const jitter=d.mode==="swarm"?(Math.random()-.5)*spread*.35:0;
    const a=ang+offset+jitter,speed=(d.speed||PROJ_SPEED)*(d.mode==="swarm"?(0.84+Math.random()*0.35):1);
    const startX=p.x+Math.cos(a)*12,startY=p.y+Math.sin(a)*12;
    const projectile={id:`${p.id}_${Date.now()}_${Math.random()}`,ownerId:p.id,ownerName:p.name,x:startX,y:startY,prevX:startX,prevY:startY,vx:Math.cos(a)*speed,vy:Math.sin(a)*speed,damage:totalDamage/shots,life:d.life||PROJ_LIFE,weaponKey:key,color:d.color,size:d.size||2.5,mode:d.mode};
    pvpProjectiles.push(projectile);
    spawned.push({id:projectile.id,ownerId:projectile.ownerId,x:projectile.x,y:projectile.y,vx:projectile.vx,vy:projectile.vy,weaponKey:projectile.weaponKey,color:projectile.color,size:projectile.size,mode:projectile.mode});
  }
  // v4.0.12: broadcast spawned bullets immediately so mobile/browser clients see
  // other players firing without waiting for the next world-state packet.
  for(const projectile of spawned)io.emit("pvpProjectileSpawn",{projectile});
  return d.cooldown||SHOOT_CD;
}

/* ── Account token + server-authoritative inventory ── */
function base64urlToJson(input){
  try{input=String(input||"").replace(/-/g,"+").replace(/_/g,"/");while(input.length%4)input+="=";return JSON.parse(Buffer.from(input,"base64").toString("utf8"));}
  catch(_){return null;}
}
function hmacSign(input,secret){return crypto.createHmac("sha256",secret).update(input).digest("base64").replace(/=/g,"").replace(/\+/g,"-").replace(/\//g,"_");}
function verifyGameToken(token){
  if(!token||!WIX_GAME_AUTH_SECRET)return null;
  const [h,p,s]=String(token).split(".");if(!h||!p||!s)return null;
  const expected=hmacSign(`${h}.${p}`,WIX_GAME_AUTH_SECRET);
  if(s!==expected)return null;
  const data=base64urlToJson(p);if(!data||!data.memberId)return null;
  if(data.exp&&Date.now()>Number(data.exp))return null;
  return data;
}
function emptySlots(n=24){return Array(n).fill(null).map(()=>({type:null,count:0}));}
function normalizeInventorySlots(slots,maxSlots=24){
  maxSlots=Math.max(24,Math.min(96,Math.floor(Number(maxSlots)||24)));
  const out=emptySlots(maxSlots);
  if(Array.isArray(slots)){
    for(let i=0;i<Math.min(slots.length,maxSlots);i++){
      const type=String(slots[i]?.type||"");const count=Math.max(0,Math.min(9999,Math.floor(Number(slots[i]?.count)||0)));
      if(type&&isInventoryItemKey(type)&&count>0)out[i]={type,count};
    }
  }else if(slots&&typeof slots==="object"){
    let idx=0;
    for(const [type,val] of Object.entries(slots)){
      let count=Math.max(0,Math.min(9999,Math.floor(Number(val)||0)));
      if(!isInventoryItemKey(type)||count<=0)continue;
      while(count>0&&idx<maxSlots){const put=Math.min(24,count);out[idx++]={type,count:put};count-=put;}
    }
  }
  return out;
}
function getAuthInventoryPayload(auth){
  if(!auth||typeof auth!=="object")return undefined;
  if(auth.invSlots!==undefined)return auth.invSlots;
  if(auth.inventory!==undefined)return auth.inventory;
  if(auth.items!==undefined)return auth.items;
  return undefined;
}
function authHasInventoryPayload(auth){return getAuthInventoryPayload(auth)!==undefined;}
function inventoryPayloadHasItems(payload){
  if(Array.isArray(payload))return payload.some(s=>s&&isInventoryItemKey(String(s.type||""))&&Math.floor(Number(s.count)||0)>0);
  if(payload&&typeof payload==="object"){
    return Object.entries(payload).some(([type,val])=>isInventoryItemKey(type)&&Math.floor(Number(val)||0)>0);
  }
  return false;
}
function objectHasAnyValue(obj){
  if(!obj||typeof obj!=="object")return false;
  return Object.keys(obj).length>0;
}
function authHasNonDefaultProgress(auth){
  if(!auth||typeof auth!=="object")return false;
  if(Number(auth.credits)>300)return true;
  if(Number(auth.maxSlots)>24)return true;
  if(auth.shipType&&auth.shipType!=="scout")return true;
  if(Number(auth.level)>1||Number(auth.xp)>0)return true;
  if(Array.isArray(auth.activeMercs)&&auth.activeMercs.length>0)return true;
  if(objectHasAnyValue(auth.buildings)||objectHasAnyValue(auth.badgeRewards)||Number(auth.storyProgress?.completed)>0)return true;
  if(auth.attrs&&typeof auth.attrs==="object"&&Object.entries(auth.attrs).some(([_,v])=>Number(v)>1))return true;
  if(auth.weaponLevels&&typeof auth.weaponLevels==="object"&&Object.entries(auth.weaponLevels).some(([k,v])=>isWeaponKey(k)&&Number(v)>1))return true;
  if(auth.equippedWeapon&&auth.equippedWeapon!=="weapon_laser_mk1")return true;
  if(objectHasAnyValue(auth.cosmeticInventory)||objectHasAnyValue(auth.redeemedCoupons)||Object.values(auth.equippedCosmetics||{}).some(Boolean))return true;
  return false;
}
function authSnapshotExplicitlyReady(auth){
  return !!(auth&&(auth.persistenceLoaded===true||auth.savedGameReady===true||auth.snapshotReady===true||auth.inventoryReady===true||auth.allowEmptyInventory===true));
}
function authClaimsFreshEmptyAccount(auth){
  return !!(auth&&(auth.signupCreditBonusEligible===true||auth.isNewMember===true||auth.newMember===true||auth.noSavedGame===true||auth.savedGameMissing===true||auth.freshAccount===true));
}
function isDefaultEmptyAccountSnapshot(auth){
  if(!auth||typeof auth!=="object")return true;
  const inv=getAuthInventoryPayload(auth);
  return !inventoryPayloadHasItems(inv)&&!authHasNonDefaultProgress(auth);
}
function isTrustedAccountSnapshot(auth){
  if(!auth||typeof auth!=="object")return false;
  const inv=getAuthInventoryPayload(auth);
  if(inv!==undefined&&inventoryPayloadHasItems(inv))return true;
  if(authHasNonDefaultProgress(auth))return true;
  // A default/empty snapshot is only safe when Wix explicitly says the account is
  // new or has no saved game. A generic persistenceLoaded:true empty payload is
  // not trusted anymore because it can erase an existing account if Wix posts a
  // startup/default fallback before the real save is available.
  if(authSnapshotExplicitlyReady(auth)&&authClaimsFreshEmptyAccount(auth))return true;
  return false;
}
function playerHasSaveWorthyProgress(p){
  if(!p)return false;
  if((p.credits||0)>300)return true;
  if((p.maxSlots||24)>24)return true;
  if(inventoryPayloadHasItems(p.invSlots))return true;
  if((p.level||1)>1||(p.xp||0)>0)return true;
  if(p.shipType&&p.shipType!=="scout")return true;
  if(Array.isArray(p.activeMercs)&&p.activeMercs.length>0)return true;
  if(objectHasAnyValue(p.savedBuildings)||objectHasAnyValue(p.badgeRewards)||Number(p.storyProgress?.completed)>0)return true;
  if(p.attrs&&Object.entries(p.attrs).some(([_,v])=>Number(v)>1))return true;
  if(p.weaponLevels&&Object.entries(p.weaponLevels).some(([k,v])=>isWeaponKey(k)&&Number(v)>1))return true;
  if(Object.values(normalizePlanetModules(p.planetModules||{})).some(v=>v>0))return true;
  if(p.equippedWeapon&&p.equippedWeapon!=="weapon_laser_mk1")return true;
  if(objectHasAnyValue(p.cosmeticInventory)||objectHasAnyValue(p.redeemedCoupons)||Object.values(p.equippedCosmetics||{}).some(Boolean))return true;
  return false;
}
function trustedSnapshotForPlayer(p,reason="cache"){
  if(!p?.memberId)return null;
  return {memberId:String(p.memberId),displayName:p.name,credits:p.credits||0,maxSlots:p.maxSlots||24,invSlots:normalizeInventorySlots(p.invSlots||emptySlots(p.maxSlots||24),p.maxSlots||24),level:p.level||1,xp:p.xp||0,shipType:p.shipType||"scout",attrs:p.attrs||{},badgeRewards:p.badgeRewards||{},storyProgress:normalizeStoryProgress(p.storyProgress||{}),equippedWeapon:p.equippedWeapon||"weapon_laser_mk1",weaponLevels:p.weaponLevels||{weapon_laser_mk1:1},equippedAttachments:normalizeAttachments(p.equippedAttachments||{}),planetModules:normalizePlanetModules(p.planetModules||{}),activeMercs:(p.activeMercs||[]).map(publicMerc),buildings:buildingSnapshotForPlayer(p),cosmeticInventory:normalizeCosmeticInventory(p.cosmeticInventory||{}),equippedCosmetics:normalizeEquippedCosmetics(p.equippedCosmetics||{}),stationTierCosmetics:normalizeStationTierCosmetics(p.stationTierCosmetics||{}),planetTypeCosmetics:normalizePlanetTypeCosmetics(p.planetTypeCosmetics||{}),redeemedCoupons:normalizeRedeemedCoupons(p.redeemedCoupons||{}),signupCreditBonusGranted:!!p.signupCreditBonusGranted,persistenceLoaded:true,savedGameReady:true,reason,updatedAt:Date.now()};
}
function rememberTrustedSnapshot(p,reason="update"){
  if(!p?.memberId||!p.persistenceLoaded)return;
  const snap=trustedSnapshotForPlayer(p,reason);
  if(snap)accountLastGoodSnapshots.set(String(p.memberId),snap);
}
function patchAuthWithCachedSnapshotIfSafer(auth){
  if(!auth?.memberId)return auth;
  const memberId=String(auth.memberId);
  const cached=accountLastGoodSnapshots.get(memberId);
  if(!cached)return auth;
  const incomingTrusted=isTrustedAccountSnapshot(auth);
  const incomingHasItems=inventoryPayloadHasItems(getAuthInventoryPayload(auth));
  const cachedHasItems=inventoryPayloadHasItems(cached.invSlots);
  // If Wix/browser posts an empty or partial startup payload, never let it erase
  // a trusted snapshot we already saw/saved during this server process.
  if(!incomingTrusted||(cachedHasItems&&!incomingHasItems&&!authHasNonDefaultProgress(auth))){
    return {...cached,memberId,displayName:auth.displayName||cached.displayName};
  }
  return auth;
}
function slotCountNeededForInventoryPayload(payload){
  if(Array.isArray(payload))return Math.max(24,Math.min(96,payload.length||24));
  if(payload&&typeof payload==="object"){
    let stacks=0;
    for(const [type,val] of Object.entries(payload)){
      if(!isInventoryItemKey(type))continue;
      const count=Math.max(0,Math.floor(Number(val)||0));
      if(count>0)stacks+=Math.ceil(count/24);
    }
    return Math.max(24,Math.min(96,stacks||24));
  }
  return 24;
}
function cleanClientWixSnapshot(snapshot,memberId){
  if(!snapshot||typeof snapshot!=="object")return null;
  if(snapshot.memberId&&String(snapshot.memberId)!==String(memberId))return null;
  const out={memberId:String(memberId)};
  if(typeof snapshot.displayName==="string")out.displayName=sanitizeName(snapshot.displayName);
  if(typeof snapshot.credits==="number"&&Number.isFinite(snapshot.credits))out.credits=Math.max(0,Math.floor(snapshot.credits));
  if(typeof snapshot.maxSlots==="number"&&Number.isFinite(snapshot.maxSlots))out.maxSlots=Math.max(24,Math.min(96,Math.floor(snapshot.maxSlots)));
  if(Array.isArray(snapshot.invSlots))out.invSlots=snapshot.invSlots;
  else if(snapshot.inventory&&typeof snapshot.inventory==="object")out.inventory=snapshot.inventory;
  else if(snapshot.items&&typeof snapshot.items==="object")out.items=snapshot.items;
  if(typeof snapshot.shipType==="string"&&SHIP_TYPES[snapshot.shipType])out.shipType=snapshot.shipType;
  if(typeof snapshot.level==="number")out.level=Math.max(1,Math.floor(snapshot.level));
  if(typeof snapshot.xp==="number")out.xp=Math.max(0,Math.floor(snapshot.xp));
  if(snapshot.attrs&&typeof snapshot.attrs==="object")out.attrs=snapshot.attrs;
  if(snapshot.badgeRewards&&typeof snapshot.badgeRewards==="object")out.badgeRewards=snapshot.badgeRewards;
  if(snapshot.storyProgress&&typeof snapshot.storyProgress==="object")out.storyProgress=normalizeStoryProgress(snapshot.storyProgress);
  if(typeof snapshot.equippedWeapon==="string"&&isWeaponKey(snapshot.equippedWeapon))out.equippedWeapon=snapshot.equippedWeapon;
  if(snapshot.weaponLevels&&typeof snapshot.weaponLevels==="object")out.weaponLevels=snapshot.weaponLevels;
  if(snapshot.equippedAttachments&&typeof snapshot.equippedAttachments==="object")out.equippedAttachments=normalizeAttachments(snapshot.equippedAttachments);
  if(snapshot.planetModules&&typeof snapshot.planetModules==="object")out.planetModules=normalizePlanetModules(snapshot.planetModules);
  if(Array.isArray(snapshot.activeMercs))out.activeMercs=snapshot.activeMercs;
  if(snapshot.buildings&&typeof snapshot.buildings==="object")out.buildings=snapshot.buildings;
  if(snapshot.cosmeticInventory&&typeof snapshot.cosmeticInventory==="object")out.cosmeticInventory=normalizeCosmeticInventory(snapshot.cosmeticInventory);
  if(snapshot.equippedCosmetics&&typeof snapshot.equippedCosmetics==="object")out.equippedCosmetics=normalizeEquippedCosmetics(snapshot.equippedCosmetics);
  if(snapshot.stationTierCosmetics&&typeof snapshot.stationTierCosmetics==="object")out.stationTierCosmetics=normalizeStationTierCosmetics(snapshot.stationTierCosmetics);
  if(snapshot.planetTypeCosmetics&&typeof snapshot.planetTypeCosmetics==="object")out.planetTypeCosmetics=normalizePlanetTypeCosmetics(snapshot.planetTypeCosmetics);
  if(snapshot.redeemedCoupons&&typeof snapshot.redeemedCoupons==="object")out.redeemedCoupons=normalizeRedeemedCoupons(snapshot.redeemedCoupons);
  if(snapshot.signupCreditBonusGranted===true||snapshot.accountCreationBonusGranted===true)out.signupCreditBonusGranted=true;
  if(snapshot.signupCreditBonusEligible===true||snapshot.isNewMember===true||snapshot.newMember===true)out.signupCreditBonusEligible=true;
  if(snapshot.isNewMember===true)out.isNewMember=true;
  if(snapshot.newMember===true)out.newMember=true;
  if(snapshot.noSavedGame===true||snapshot.savedGameMissing===true||snapshot.freshAccount===true){
    if(snapshot.noSavedGame===true)out.noSavedGame=true;
    if(snapshot.savedGameMissing===true)out.savedGameMissing=true;
    if(snapshot.freshAccount===true)out.freshAccount=true;
  }
  if(typeof snapshot.accountCreatedAt==="string"||typeof snapshot.accountCreatedAt==="number")out.accountCreatedAt=snapshot.accountCreatedAt;
  for(const flag of ["persistenceLoaded","savedGameReady","snapshotReady","inventoryReady","allowEmptyInventory"]){
    if(snapshot[flag]===true)out[flag]=true;
  }
  return out;
}
function combineAuthWithClientSnapshot(auth,snapshot){
  if(!auth)return auth;
  const snap=cleanClientWixSnapshot(snapshot,auth.memberId);
  if(!snap)return auth;
  const out={...auth};
  // Signed token data wins when it contains a value. The snapshot fills gaps when
  // Wix sends member auth separately from the persisted inventory payload.
  for(const k of ["displayName","credits","maxSlots","shipType","level","xp","attrs","badgeRewards","storyProgress","equippedAttachments","planetModules","activeMercs","buildings","cosmeticInventory","equippedCosmetics","stationTierCosmetics","planetTypeCosmetics","redeemedCoupons","signupCreditBonusGranted","signupCreditBonusEligible","isNewMember","newMember","noSavedGame","savedGameMissing","freshAccount","accountCreatedAt","persistenceLoaded","savedGameReady","snapshotReady","inventoryReady","allowEmptyInventory"]){
    if(out[k]===undefined&&snap[k]!==undefined)out[k]=snap[k];
  }
  if(!authHasInventoryPayload(out)&&authHasInventoryPayload(snap)){
    if(snap.invSlots!==undefined)out.invSlots=snap.invSlots;
    else if(snap.inventory!==undefined)out.inventory=snap.inventory;
    else if(snap.items!==undefined)out.items=snap.items;
  }
  return out;
}
function extractPersistedSnapshotFromWixResponse(data,memberId){
  if(!data||typeof data!=="object")return null;
  const raw=data.player||data.snapshot||data.save||data.record||data.data||data;
  return cleanClientWixSnapshot(raw,memberId);
}
async function loadPersistedAccountSnapshot(memberId){
  memberId=String(memberId||"");
  if(!memberId||!WIX_LOAD_URL||!WIX_PERSIST_SECRET)return null;
  try{
    const url=new URL(WIX_LOAD_URL);
    url.searchParams.set("memberId",memberId);
    url.searchParams.set("t",String(Date.now()));
    const res=await fetch(url.toString(),{method:"GET",headers:{"Authorization":`Bearer ${WIX_PERSIST_SECRET}`}});
    if(!res.ok){console.warn("Wix load failed response:",res.status);return null;}
    const data=await res.json().catch(()=>null);
    if(!data||data.ok===false)return null;
    const snap=extractPersistedSnapshotFromWixResponse(data,memberId);
    return snap&&isTrustedAccountSnapshot(snap)?snap:null;
  }catch(err){console.warn("Wix load failed:",err?.message||err);return null;}
}
async function enrichAuthWithPersistedSnapshot(auth,context="auth"){
  if(!auth?.memberId)return auth;
  auth=patchAuthWithCachedSnapshotIfSafer(auth);
  if(isTrustedAccountSnapshot(auth))return auth;
  const loaded=await loadPersistedAccountSnapshot(auth.memberId);
  if(!loaded)return auth;
  return patchAuthWithCachedSnapshotIfSafer({...auth,...loaded,memberId:String(auth.memberId),displayName:auth.displayName||loaded.displayName});
}
function inventoryFingerprint(slots,maxSlots=24,credits=0){
  const norm=normalizeInventorySlots(slots,maxSlots);
  return `${Math.max(0,Math.floor(Number(credits)||0))}|${maxSlots}|`+norm.map(s=>s?.type?`${s.type}:${s.count}`:"-").join(",");
}
function inventoryCounts(p){const o={};for(const s of p.invSlots||[])if(s?.type&&s.count>0)o[s.type]=(o[s.type]||0)+s.count;return o;}
function inventoryCount(p,type){let n=0;for(const s of p.invSlots||[])if(s.type===type)n+=s.count;return n;}
function canFitInventory(p,type,amount){
  let rem=Math.max(0,Math.floor(Number(amount)||0));if(rem<=0)return true;
  for(let i=0;i<(p.maxSlots||24);i++){const s=p.invSlots[i];if(s?.type===type&&s.count<24)rem-=Math.min(24-s.count,rem);if(rem<=0)return true;}
  for(let i=0;i<(p.maxSlots||24);i++){const s=p.invSlots[i];if(!s?.type){rem-=Math.min(24,rem);if(rem<=0)return true;}}
  return false;
}
function addInventory(p,type,amount){
  if(!isInventoryItemKey(type))return false;
  let rem=Math.max(0,Math.floor(Number(amount)||0));if(rem<=0)return true;
  if(!Array.isArray(p.invSlots))p.invSlots=emptySlots(p.maxSlots||24);
  for(let i=0;i<(p.maxSlots||24);i++){const s=p.invSlots[i];if(s?.type===type&&s.count<24){const add=Math.min(24-s.count,rem);s.count+=add;rem-=add;if(rem<=0)return true;}}
  for(let i=0;i<(p.maxSlots||24);i++){const s=p.invSlots[i];if(!s?.type){const add=Math.min(24,rem);p.invSlots[i]={type,count:add};rem-=add;if(rem<=0)return true;}}
  return false;
}
function removeInventory(p,type,amount){
  let rem=Math.max(0,Math.floor(Number(amount)||0));if(rem<=0)return true;
  if(inventoryCount(p,type)<rem)return false;
  for(let i=(p.maxSlots||24)-1;i>=0;i--){const s=p.invSlots[i];if(s?.type===type){const rm=Math.min(s.count,rem);s.count-=rm;rem-=rm;if(s.count<=0)p.invSlots[i]={type:null,count:0};if(rem<=0)return true;}}
  return true;
}
// Upgrades replace an existing item stack.  Check capacity after the source
// copies are removed so a completely full inventory can still transform a
// module in-place rather than producing a misleading "inventory full" error.
function canReplaceInventoryItem(p,from,removeAmount,to,addAmount=1){
  const maxSlots=Math.max(24,Math.floor(Number(p?.maxSlots)||24));
  const sim={maxSlots,invSlots:emptySlots(maxSlots)};
  for(let i=0;i<maxSlots;i++){
    const s=p?.invSlots?.[i];
    if(s?.type&&s.count>0)sim.invSlots[i]={type:s.type,count:s.count};
  }
  return removeInventory(sim,from,removeAmount)&&canFitInventory(sim,to,addAmount);
}
function recipeItems(recipe){return Object.entries(recipe||{}).filter(([k,v])=>k!=="credits"&&RES_KEYS.includes(k)&&Math.floor(Number(v)||0)>0).map(([type,qty])=>({type,qty:Math.floor(Number(qty)||0)}));}
function canCraftRecipe(p,recipe){
  const credits=Math.max(0,Math.floor(Number(recipe?.credits)||0));
  if((p.credits||0)<credits)return {ok:false,reason:`Need ${credits} credits.`};
  for(const it of recipeItems(recipe)){if(inventoryCount(p,it.type)<it.qty)return {ok:false,reason:`Need ${it.qty}x ${it.type}.`};}
  return {ok:true};
}
function consumeCraftRecipe(p,recipe){for(const it of recipeItems(recipe))removeInventory(p,it.type,it.qty);p.credits=(p.credits||0)-Math.max(0,Math.floor(Number(recipe?.credits)||0));}

function attrUpgradeCost(p,attr){
  const cur=Math.max(1,Math.floor(Number(p?.attrs?.[attr])||1));
  return {
    credits:Math.floor(500*Math.pow(1.55,cur-1)),
    xp:Math.floor(80*Math.pow(1.38,cur-1))
  };
}
function grantRewardBundle(p,{credits=0,xp=0,items=[]}={},reason="reward"){
  credits=Math.max(0,Math.min(100000,Math.floor(Number(credits)||0)));
  xp=Math.max(0,Math.min(25000,Math.floor(Number(xp)||0)));
  const normalized=[];
  for(const it of Array.isArray(items)?items:[]){const type=String(it.type||"");const qty=Math.max(1,Math.min(48,Math.floor(Number(it.qty)||0)));if(isInventoryItemKey(type))normalized.push({type,qty});}
  for(const it of normalized){if(!canFitInventory(p,it.type,it.qty))return {ok:false,reason:"Inventory full for reward items."};}
  if(credits>0)p.credits=(p.credits||0)+credits;
  for(const it of normalized)addInventory(p,it.type,it.qty);
  if(xp>0)grantXp(p,xp,reason);
  return {ok:true,credits,xp,items:normalized};
}
function validateTradeItems(p,items){
  const need={};for(const it of items||[]){const type=String(it.type||"");const q=Math.max(0,Math.floor(Number(it.quantity)||0));if(!isInventoryItemKey(type)||q<=0)return false;need[type]=(need[type]||0)+q;}
  return Object.entries(need).every(([type,q])=>inventoryCount(p,type)>=q);
}
function emitInventorySync(p,reason="sync"){
  if(!p?.id)return;
  io.to(p.id).emit("inventorySync",{
    credits:p.credits||0,maxSlots:p.maxSlots||24,invSlots:p.invSlots||emptySlots(24),inventory:inventoryCounts(p),
    level:p.level||1,xp:p.xp||0,xpToNext:playerXpNeeded(p.level||1),attrPoints:p.attrPoints||0,attrs:p.attrs||{},
    equippedWeapon:p.equippedWeapon||"weapon_laser_mk1",weaponLevels:p.weaponLevels||{weapon_laser_mk1:1},
    equippedAttachments:normalizeAttachments(p.equippedAttachments||{}),attachmentDefs:ATTACHMENT_DEFS,planetModules:normalizePlanetModules(p.planetModules||{}),moduleDefs:publicPlanetModuleDefs(),storyProgress:normalizeStoryProgress(p.storyProgress||{}),reason,
    persistenceLoaded:!!p.persistenceLoaded,accountLoaded:!!p.accountLoaded,memberId:p.memberId||null
  });
}
async function persistPlayerNow(p,reason="update"){
  if(!p?.memberId){console.warn("Wix persistence skipped: player has no memberId", p?.id, reason);return;}
  if(p.suppressPersist||!isCurrentAccountSocket(p)){console.warn("Wix persistence skipped: superseded account socket", p?.id, p?.memberId, reason);return;}
  if(!p.persistenceLoaded){console.warn("Wix persistence skipped: account inventory snapshot not loaded yet", p?.id, p?.memberId, reason);return;}
  if(!playerHasSaveWorthyProgress(p)&&!p.signupCreditBonusGranted){console.warn("Wix persistence skipped: refusing to save empty/default account snapshot", p?.id, p?.memberId, reason);return;}
  if(!WIX_PERSIST_URL||!WIX_PERSIST_SECRET){console.warn("Wix persistence skipped: missing WIX_PERSIST_URL or WIX_PERSIST_SECRET", {hasUrl:!!WIX_PERSIST_URL,hasSecret:!!WIX_PERSIST_SECRET});return;}
  const payload={memberId:p.memberId,displayName:p.name,credits:p.credits||0,maxSlots:p.maxSlots||24,invSlots:p.invSlots||emptySlots(24),level:p.level||1,xp:p.xp||0,shipType:p.shipType||"scout",attrs:p.attrs||{},badgeRewards:p.badgeRewards||{},storyProgress:normalizeStoryProgress(p.storyProgress||{}),equippedWeapon:p.equippedWeapon||"weapon_laser_mk1",weaponLevels:p.weaponLevels||{weapon_laser_mk1:1},equippedAttachments:normalizeAttachments(p.equippedAttachments||{}),planetModules:normalizePlanetModules(p.planetModules||{}),activeMercs:(p.activeMercs||[]).map(publicMerc),buildings:buildingSnapshotForPlayer(p),cosmeticInventory:normalizeCosmeticInventory(p.cosmeticInventory||{}),equippedCosmetics:normalizeEquippedCosmetics(p.equippedCosmetics||{}),stationTierCosmetics:normalizeStationTierCosmetics(p.stationTierCosmetics||{}),planetTypeCosmetics:normalizePlanetTypeCosmetics(p.planetTypeCosmetics||{}),redeemedCoupons:normalizeRedeemedCoupons(p.redeemedCoupons||{}),signupCreditBonusGranted:!!p.signupCreditBonusGranted,reason,updatedAt:Date.now()};
  try{
    const res = await fetch(WIX_PERSIST_URL,{method:"POST",headers:{"Content-Type":"application/json","Authorization":`Bearer ${WIX_PERSIST_SECRET}`},body:JSON.stringify(payload)});
    if(!res.ok){
      const text = await res.text().catch(()=>"");
      console.warn("Wix persistence failed response:", res.status, text.slice(0,300));
    }else{
      rememberTrustedSnapshot(p,reason);
    }
  }catch(err){console.warn("Wix persistence failed:",err?.message||err);}
}
function persistPlayerSoon(p,reason="update",delay=1200){
  if(!p?.memberId)return;
  if(p.suppressPersist||!isCurrentAccountSocket(p))return;
  if(!p.persistenceLoaded){console.warn("Wix persistence delayed/skipped until inventory snapshot loads", p?.id, p?.memberId, reason);return;}
  if(persistTimers.has(p.id))clearTimeout(persistTimers.get(p.id));
  persistTimers.set(p.id,setTimeout(()=>{persistTimers.delete(p.id);persistPlayerNow(p,reason);},delay));
}
function syncAndPersist(p,reason="sync"){
  emitInventorySync(p,reason);persistPlayerSoon(p,reason);
}
function hasInventoryItems(slots){return Array.isArray(slots)&&slots.some(s=>s?.type&&s.count>0);}
function mergeInventoryIntoPlayer(p,slotsOrCounts){
  const incoming=normalizeInventorySlots(slotsOrCounts,p.maxSlots||24);
  for(const s of incoming){if(s?.type&&s.count>0)addInventory(p,s.type,s.count);}
}
function applyAuthAccountToPlayer(p,auth){
  if(!auth)return;
  auth=patchAuthWithCachedSnapshotIfSafer(auth);
  const memberId=String(auth.memberId||"");
  if(memberId)p.memberId=memberId;
  p.accountLoaded=true;
  if(auth.signupCreditBonusGranted===true)p.signupCreditBonusGranted=true;
  if(auth.signupCreditBonusEligible===true)p.signupCreditBonusEligible=true;
  if(auth.accountCreatedAt!==undefined)p.accountCreatedAt=auth.accountCreatedAt;
  p.name=sanitizeName(auth.displayName||p.name||"Pilot");
  const authInventory=getAuthInventoryPayload(auth);
  const trustedSnapshot=isTrustedAccountSnapshot(auth);

  let desiredSlots;
  if(auth.maxSlots!==undefined){
    const slots=Number(auth.maxSlots);
    if(Number.isFinite(slots))desiredSlots=Math.max(24,Math.min(96,Math.floor(slots)));
  }
  if(desiredSlots===undefined&&Array.isArray(authInventory))desiredSlots=Math.max(24,Math.min(96,authInventory.length||24));
  if(desiredSlots===undefined&&authInventory&&typeof authInventory==="object")desiredSlots=slotCountNeededForInventoryPayload(authInventory);
  if(desiredSlots===undefined)desiredSlots=Math.max(24,Math.min(96,Math.floor(Number(p.maxSlots)||24)));
  p.maxSlots=desiredSlots;

  if(auth.credits!==undefined&&trustedSnapshot){
    const credits=Number(auth.credits);
    if(Number.isFinite(credits))p.credits=Math.max(0,Math.floor(credits));
  }else if(auth.credits!==undefined&&Number(auth.credits)>300){
    const credits=Number(auth.credits);
    if(Number.isFinite(credits))p.credits=Math.max(0,Math.floor(credits));
  }
  if(authInventory!==undefined&&trustedSnapshot){
    p.invSlots=normalizeInventorySlots(authInventory,p.maxSlots);
    p.persistenceLoaded=true;
    p.loadedInventoryFingerprint=inventoryFingerprint(p.invSlots,p.maxSlots,p.credits||0);
    rememberTrustedSnapshot(p,"account_snapshot_loaded");
  }else{
    if(authInventory!==undefined&&!trustedSnapshot){
      console.warn("Ignored untrusted/default Wix inventory payload so it cannot reset account progress", p.id, memberId);
    }
    // Never replace an existing/default inventory with an empty array just because
    // the auth token did not contain inventory. That was one source of lost saves.
    if(!Array.isArray(p.invSlots))p.invSlots=emptySlots(p.maxSlots);
    if(p.invSlots.length<p.maxSlots){
      while(p.invSlots.length<p.maxSlots)p.invSlots.push({type:null,count:0});
    }else if(p.invSlots.length>p.maxSlots)p.invSlots.length=p.maxSlots;
  }
  if(auth.shipType&&SHIP_TYPES[auth.shipType])p.shipType=auth.shipType;
  if(auth.level)p.level=Math.max(1,Math.floor(Number(auth.level)||1));
  if(auth.xp!==undefined)p.xp=Math.max(0,Math.floor(Number(auth.xp)||0));
  if(auth.attrs&&typeof auth.attrs==="object")p.attrs={...p.attrs,...auth.attrs};
  if(auth.badgeRewards&&typeof auth.badgeRewards==="object")p.badgeRewards={...auth.badgeRewards};
  if(auth.storyProgress&&typeof auth.storyProgress==="object"){const incoming=normalizeStoryProgress(auth.storyProgress),cur=normalizeStoryProgress(p.storyProgress||{});p.storyProgress=normalizeStoryProgress({completed:Math.max(cur.completed,incoming.completed),startedAt:Math.min(cur.startedAt,incoming.startedAt),updatedAt:Math.max(cur.updatedAt,incoming.updatedAt)});}
  if(auth.weaponLevels&&typeof auth.weaponLevels==="object"){p.weaponLevels={...(p.weaponLevels||{})};for(const [k,v] of Object.entries(auth.weaponLevels)){if(isWeaponKey(k)){const lvl=Math.max(1,Math.min(20,Math.floor(Number(v)||1)));p.weaponLevels[k]=lvl;}}}
  if(typeof auth.equippedWeapon==="string"&&isWeaponKey(auth.equippedWeapon))p.equippedWeapon=auth.equippedWeapon;
  if(auth.equippedAttachments&&typeof auth.equippedAttachments==="object")p.equippedAttachments=normalizeAttachments(auth.equippedAttachments);
  if(auth.planetModules&&typeof auth.planetModules==="object")p.planetModules=normalizePlanetModules(auth.planetModules);
  applyShipStats(p,false);
  if(Array.isArray(auth.activeMercs))p.activeMercs=normalizeMercs(auth.activeMercs,p);
  if(auth.buildings&&typeof auth.buildings==="object")p.savedBuildings=auth.buildings;
  if(auth.cosmeticInventory&&typeof auth.cosmeticInventory==="object")p.cosmeticInventory=normalizeCosmeticInventory(auth.cosmeticInventory);
  if(auth.equippedCosmetics&&typeof auth.equippedCosmetics==="object")p.equippedCosmetics=normalizeEquippedCosmetics(auth.equippedCosmetics);
  if(auth.stationTierCosmetics&&typeof auth.stationTierCosmetics==="object")p.stationTierCosmetics=normalizeStationTierCosmetics(auth.stationTierCosmetics);
  if(auth.planetTypeCosmetics&&typeof auth.planetTypeCosmetics==="object")p.planetTypeCosmetics=normalizePlanetTypeCosmetics(auth.planetTypeCosmetics);
  if(auth.redeemedCoupons&&typeof auth.redeemedCoupons==="object")p.redeemedCoupons=normalizeRedeemedCoupons(auth.redeemedCoupons);
}
function applyPersistedSnapshotPreservingSession(p,auth){
  const currentCounts=inventoryCounts({invSlots:p.invSlots||emptySlots(p.maxSlots||24)});
  const currentCredits=Math.floor(Number(p.credits)||300);
  const sessionCreditDelta=currentCredits-300;
  applyAuthAccountToPlayer(p,auth);
  for(const [type,count] of Object.entries(currentCounts)){
    if(count>0&&!addInventory(p,type,count)){
      // Module instances are inventory keys too; use their base item/economy
      // value instead of treating an upgraded module as a 1-credit fallback.
      p.credits=(p.credits||0)+Math.max(1,economy.price(type)||RES_BASE[inventoryBaseType(type)]||1)*count;
    }
  }
  if(sessionCreditDelta!==0)p.credits=Math.max(0,(p.credits||0)+sessionCreditDelta);
}
function linkAuthAccountToPlayer(p,auth){
  if(!auth)return {ok:false,alreadyLinked:false};
  auth=patchAuthWithCachedSnapshotIfSafer(auth);
  const memberId=String(auth.memberId||"");
  if(!memberId)return {ok:false,alreadyLinked:false};
  const hasSnapshot=authHasInventoryPayload(auth);
  const trustedSnapshot=isTrustedAccountSnapshot(auth);

  // Repeated auth pings for the same account are harmless. If the first ping had
  // only memberId and the later ping carries the real Wix inventory snapshot,
  // apply that snapshot once and preserve items earned during the short guest window.
  if(p.accountLoaded&&String(p.memberId||"")===memberId){
    p.name=sanitizeName(auth.displayName||p.name||"Pilot");
    if(!p.persistenceLoaded&&hasSnapshot&&trustedSnapshot){
      applyPersistedSnapshotPreservingSession(p,auth);
      return {ok:true,alreadyLinked:false,lateSnapshot:true};
    }
    if(!p.persistenceLoaded&&hasSnapshot&&!trustedSnapshot){
      return {ok:true,alreadyLinked:true,waitingForTrustedSnapshot:true};
    }
    return {ok:true,alreadyLinked:true};
  }

  if(hasSnapshot&&trustedSnapshot)applyPersistedSnapshotPreservingSession(p,auth);
  else applyAuthAccountToPlayer(p,auth);
  return {ok:true,alreadyLinked:false};
}

function authEligibleForAccountCreationBonus(auth){
  if(!auth||typeof auth!=="object")return false;
  if(auth.signupCreditBonusGranted===true)return false;
  if(auth.signupCreditBonusEligible===true||auth.isNewMember===true||auth.newMember===true)return true;
  // Do not treat a generic empty/ready save as a new account. Wix must explicitly
  // tell the server this is a fresh member or a missing saved-game record.
  if(authClaimsFreshEmptyAccount(auth))return true;
  return false;
}
function maybeGrantAccountCreationBonus(p,auth,context="account_link"){
  if(!p?.memberId||ACCOUNT_CREATION_BONUS_CREDITS<=0)return {granted:false};
  const memberId=String(p.memberId);
  if(p.signupCreditBonusGranted||accountCreationBonusLocks.has(memberId))return {granted:false,alreadyGranted:true};
  if(!authEligibleForAccountCreationBonus(auth)){
    if(p.id)io.to(p.id).emit("accountCreationBonusPending",{reason:"Account linked. Waiting for Wix to confirm this is a new saved account before granting the 100,000 credit welcome bonus."});
    return {granted:false,pending:true};
  }
  if(!p.persistenceLoaded&&isTrustedAccountSnapshot(auth)){
    p.persistenceLoaded=true;
  }
  p.credits=(p.credits||0)+ACCOUNT_CREATION_BONUS_CREDITS;
  p.signupCreditBonusGranted=true;
  accountCreationBonusLocks.add(memberId);
  const grant={memberId,creditsAdded:ACCOUNT_CREATION_BONUS_CREDITS,credits:p.credits,context,grantedAt:Date.now()};
  if(p.id){
    io.to(p.id).emit("accountCreationBonusGranted",grant);
    io.to(p.id).emit("creditUpdate",{credits:p.credits});
  }
  emitInventorySync(p,"account_creation_bonus");
  persistPlayerSoon(p,"account_creation_bonus",100);
  rememberTrustedSnapshot(p,"account_creation_bonus");
  return {granted:true,grant};
}

function normalizeStorageSlots(slots,maxSlots=24){
  maxSlots=Math.max(24,Math.min(100,Math.floor(Number(maxSlots)||24)));
  const out=emptySlots(maxSlots);
  if(Array.isArray(slots)){
    for(let i=0;i<Math.min(slots.length,maxSlots);i++){
      const type=String(slots[i]?.type||"");const count=Math.max(0,Math.min(9999,Math.floor(Number(slots[i]?.count)||0)));
      if(type&&isInventoryItemKey(type)&&count>0)out[i]={type,count};
    }
  }
  return out;
}
function structureDefaultState(type){
  const def=PLAYER_STRUCTURE_TYPES[type]||PLAYER_STRUCTURE_TYPES.storage_facility;
  return {hp:def.maxHp,maxHp:def.maxHp,shield:def.maxShield,maxShield:def.maxShield,shieldRegenTimer:0,damageLevel:1,shieldLevel:1,storageShieldLevel:1,storageSlots:def.startSlots||24,invSlots:emptySlots(def.startSlots||24),destroyed:false,underAttackUntil:0};
}
function structureUpgradeCost(st,kind){
  if(kind==="storage")return Math.floor(450+Math.max(0,(st.storageSlots||24)-24)*42);
  if(kind==="storageShield")return Math.floor(1200*Math.pow(1.42,Math.max(0,(st.storageShieldLevel||1)-1)));
  const level=kind==="damage"?Math.max(1,st.damageLevel||1):Math.max(1,st.shieldLevel||1);
  return Math.floor((kind==="damage"?900:1050)*Math.pow(1.58,level-1));
}
function publicStructure(st,viewerId){
  return {
    key:st.key,type:st.type,ownerId:st.ownerId,ownerName:st.ownerName,x:Math.round(st.x),y:Math.round(st.y),
    isOwn:st.ownerId===viewerId,hp:st.hp,maxHp:st.maxHp,shield:st.shield,maxShield:st.maxShield,
    destroyed:!!st.destroyed,storageSlots:st.storageSlots||0,storageUsed:Array.isArray(st.invSlots)?st.invSlots.filter(x=>x?.type&&x.count>0).length:0,
    storage:st.ownerId===viewerId?st.invSlots:undefined,damageLevel:st.damageLevel||1,shieldLevel:st.shieldLevel||1,storageShieldLevel:st.storageShieldLevel||1,
    damage:turretDamage(st),range:turretRange(st),storageUpgradeCost:st.type==="storage_facility"&&Number(st.storageSlots||24)<100?structureUpgradeCost(st,"storage"):0,turretCosmeticKey:st.turretCosmeticKey||null
  };
}
function playerStructuresFor(viewerId){return [...ownedStructures.values()].map(st=>publicStructure(st,viewerId));}
function emitPlayerStructures(socket){socket.emit("playerStructuresList",playerStructuresFor(socket.id));}
function broadcastPlayerStructuresList(){for(const sock of io.sockets.sockets.values())emitPlayerStructures(sock);}
function turretDamage(st){return Math.floor((PLAYER_STRUCTURE_TYPES.defense_turret.baseDamage||18)*(1+0.38*Math.max(0,(st.damageLevel||1)-1)));}
function turretRange(st){return Math.floor((PLAYER_STRUCTURE_TYPES.defense_turret.baseRange||900)*(1+0.08*Math.max(0,(st.damageLevel||1)-1)));}
function canFitStorage(st,type,amount){const fake={invSlots:st.invSlots,maxSlots:st.storageSlots};return canFitInventory(fake,type,amount);}
function addStorage(st,type,amount){const fake={invSlots:st.invSlots,maxSlots:st.storageSlots};const ok=addInventory(fake,type,amount);st.invSlots=fake.invSlots;return ok;}
function removeStorage(st,type,amount){const fake={invSlots:st.invSlots,maxSlots:st.storageSlots};const ok=removeInventory(fake,type,amount);st.invSlots=fake.invSlots;return ok;}
function buildingSnapshotForPlayer(p){
  const memberId=p.memberId||"";
  const stations=[...ownedStations.values()].filter(st=>st.ownerId===p.id||(memberId&&st.ownerMemberId===memberId)).map(st=>({
    key:st.key,x:Math.round(st.x),y:Math.round(st.y),tier:st.tier,ownerName:st.ownerName,hiredShips:st.hiredShips||[],accumulatedGoods:st.accumulatedGoods||{},hp:st.hp,maxHp:st.maxHp,shield:st.shield,maxShield:st.maxShield,destroyed:!!st.destroyed,createdAt:st.createdAt||Date.now(),turretCosmeticKey:st.turretCosmeticKey||null
  }));
  const structures=[...ownedStructures.values()].filter(st=>st.ownerId===p.id||(memberId&&st.ownerMemberId===memberId)).map(st=>({
    key:st.key,type:st.type,x:Math.round(st.x),y:Math.round(st.y),ownerName:st.ownerName,hp:st.hp,maxHp:st.maxHp,shield:st.shield,maxShield:st.maxShield,storageSlots:st.storageSlots,invSlots:st.invSlots||[],damageLevel:st.damageLevel||1,shieldLevel:st.shieldLevel||1,storageShieldLevel:st.storageShieldLevel||1,destroyed:!!st.destroyed,createdAt:st.createdAt||Date.now(),turretCosmeticKey:st.turretCosmeticKey||null
  }));
  const civilizationZonesOwned=[...civilizationZones.values()].filter(z=>z.ownerId===p.id||(memberId&&z.ownerMemberId===memberId)).map(z=>({
    zoneId:z.zoneId,name:z.name,color:z.color,x:Math.round(z.x),y:Math.round(z.y),radius:z.radius,baseStationCount:z.baseStationCount,playerFounded:!!z.playerFounded,
    ownerName:z.ownerName,purchasedAt:z.purchasedAt||Date.now(),superStation:z.superStation||null,baseStations:z.baseStations||[],builtStations:z.builtStations||[],stationTasks:z.stationTasks||{},factionId:z.factionId,factionName:z.factionName,factionBonus:z.factionBonus,zoneLevel:z.zoneLevel,superStationLevel:z.superStationLevel,stockpile:z.stockpile||{},stockpileItems:z.stockpileItems||{},stockpileCapacity:z.stockpileCapacity,bankCredits:z.bankCredits||0,contracts:z.contracts||[],relations:z.relations||{},turrets:z.turrets||[],stationTierCosmetics:{},npcshipCosmeticKey:null,turretCosmeticKey:null,pendingTax:Math.floor(z.pendingTax||0),totalTaxCollected:Math.floor(z.totalTaxCollected||0)
  }));
  return {stations,structures,civilizationZones:civilizationZonesOwned,zones:civilizationZonesOwned};
}
function restorePersistentBuildingsForPlayer(p){
  if(!p?.memberId)return;
  // Reclaim already-loaded process memory buildings after reconnect.
  for(const st of ownedStations.values())if(st.ownerMemberId===p.memberId){st.ownerId=p.id;st.ownerName=p.name;}
  for(const st of ownedStructures.values())if(st.ownerMemberId===p.memberId){st.ownerId=p.id;st.ownerName=p.name;}
  for(const z of civilizationZones.values())if(z.ownerMemberId===p.memberId){z.ownerId=p.id;z.ownerName=p.name;}
  const b=p.savedBuildings||{};
  const savedZones=Array.isArray(b.civilizationZones)?b.civilizationZones:(Array.isArray(b.zones)?b.zones:[]);
  for(const rec of savedZones){
    const input=safeCivZoneInput({zoneId:rec.zoneId||rec.id,name:rec.name,color:rec.color,x:rec.x,y:rec.y,radius:rec.radius,baseStationCount:rec.baseStationCount??rec.stationCount,playerFounded:!!rec.playerFounded});
    if(!input)continue;
    let zone=civilizationZones.get(input.zoneId);
    if(!zone||zone.ownerMemberId===p.memberId||zone.ownerId===p.id){
      const built=[],seenBuilt=new Set();
      for(const st of Array.isArray(rec.builtStations)?rec.builtStations:[]){
        const tier=CIV_STATION_TIERS[st.tier]?st.tier:"standard";
        const x=Math.round(Number(st.x)||input.x),y=Math.round(Number(st.y)||input.y);
        const id=safeZoneId(st.id||`${input.zoneId}|ownedciv|${built.length}`);
        if(!id||seenBuilt.has(id))continue;
        seenBuilt.add(id);
        built.push({...civStationDefaults({tier}),...st,id,x,y,tier,ownerName:p.name,createdAt:st.createdAt||Date.now()});
        if(built.length>=30)break;
      }
      const baseStations=(Array.isArray(rec.baseStations)?rec.baseStations:[]).map((st,i)=>({...civStationDefaults({tier:CIV_STATION_TIERS[st?.tier]?st.tier:"standard"}),...st,id:safeZoneId(st?.id||`${input.zoneId}|civst|${i}`),tier:CIV_STATION_TIERS[st?.tier]?st.tier:"standard",ownerName:p.name}));
      const restored={...civZoneDefaults({zoneId:input.zoneId,zoneLevel:rec.zoneLevel||1}),...(zone||{}),...input,...rec,ownerId:p.id,ownerMemberId:p.memberId,ownerName:p.name,purchasedAt:rec.purchasedAt||Date.now(),baseStations,builtStations:built,pendingTax:Math.max(0,Math.floor(Number(rec.pendingTax)||0)),totalTaxCollected:Math.max(0,Math.floor(Number(rec.totalTaxCollected)||0)),stationTierCosmetics:{},npcshipCosmeticKey:null,turretCosmeticKey:null};ensureCivLogistics(restored);civilizationZones.set(input.zoneId,restored);
    }
  }
  collectPendingCivilizationTaxesFor(p);
  for(const rec of Array.isArray(b.stations)?b.stations:[]){
    const tier=OWNED_STATION_TIERS[rec.tier]?rec.tier:"outpost";
    const x=Math.round(Number(rec.x)||0),y=Math.round(Number(rec.y)||0),key=String(rec.key||`${Math.round(x/100)}_${Math.round(y/100)}`);
    let st=ownedStations.get(key);
    if(!st||st.ownerMemberId===p.memberId||st.ownerId===p.id){
      const base={key,ownerId:p.id,ownerMemberId:p.memberId,ownerName:p.name,x,y,tier,hiredShips:Array.isArray(rec.hiredShips)?rec.hiredShips.slice(0,20):[],accumulatedGoods:rec.accumulatedGoods||{},createdAt:rec.createdAt||Date.now(),...makeStationState(tier)};
      base.hp=Math.max(0,Math.min(base.maxHp,Number(rec.hp) || base.hp));base.shield=Math.max(0,Math.min(base.maxShield,Number(rec.shield) || base.shield));base.destroyed=!!rec.destroyed;
      ownedStations.set(key,{...(st||{}),...base});
    }
  }
  for(const rec of Array.isArray(b.structures)?b.structures:[]){
    const type=PLAYER_STRUCTURE_TYPES[rec.type]?rec.type:"storage_facility";
    const x=Math.round(Number(rec.x)||0),y=Math.round(Number(rec.y)||0),key=String(rec.key||`${type}_${Math.round(x/80)}_${Math.round(y/80)}`);
    let st=ownedStructures.get(key);
    if(!st||st.ownerMemberId===p.memberId||st.ownerId===p.id){
      const base={key,type,ownerId:p.id,ownerMemberId:p.memberId,ownerName:p.name,x,y,createdAt:rec.createdAt||Date.now(),...structureDefaultState(type)};if(type==="defense_turret")base.turretCosmeticKey=rec.turretCosmeticKey||p.equippedCosmetics?.turret||null;
      base.storageSlots=Math.max(24,Math.min(100,Math.floor(Number(rec.storageSlots)||base.storageSlots||24)));
      base.invSlots=normalizeStorageSlots(rec.invSlots,base.storageSlots);
      base.damageLevel=Math.max(1,Math.min(12,Math.floor(Number(rec.damageLevel)||1)));
      base.shieldLevel=Math.max(1,Math.min(12,Math.floor(Number(rec.shieldLevel)||1)));
      base.storageShieldLevel=Math.max(1,Math.floor(Number(rec.storageShieldLevel)||1));
      if(type==="storage_facility")base.maxShield=Math.floor(base.maxShield*Math.pow(1.18,base.storageShieldLevel-1));
      base.maxShield=Math.floor(base.maxShield*(1+0.32*(base.shieldLevel-1)));
      base.shield=Math.max(0,Math.min(base.maxShield,Number(rec.shield)||base.shield));base.hp=Math.max(0,Math.min(base.maxHp,Number(rec.hp)||base.hp));base.destroyed=!!rec.destroyed;
      ownedStructures.set(key,{...(st||{}),...base});
    }
  }
}
function tickPlayerStructures(dt){
  for(const st of ownedStructures.values()){
    if(st.destroyed)continue;
    st.shieldRegenTimer=Math.max(0,(st.shieldRegenTimer||0)-dt);
    if(st.shieldRegenTimer<=0&&st.shield<st.maxShield){const def=PLAYER_STRUCTURE_TYPES[st.type]||PLAYER_STRUCTURE_TYPES.storage_facility;st.shield=Math.min(st.maxShield,st.shield+(def.shieldRegen||10)*dt);}
  }
}
function applyStructureDamage(st,rawDamage){
  const raw=Math.max(0,Math.min(250,Number(rawDamage)||0));if(raw<=0||!st||st.destroyed)return {damage:0,destroyed:false};
  let dmg=raw;if(st.shield>0){const abs=Math.min(st.shield,dmg);st.shield-=abs;dmg-=abs;}if(dmg>0)st.hp=Math.max(0,st.hp-dmg);
  st.shieldRegenTimer=6;st.underAttackUntil=Date.now()+35000;return {damage:raw,destroyed:st.hp<=0};
}
function pickMercRarity(rng){let total=MERC_RARITIES.reduce((a,b)=>a+b.weight,0),roll=rng()*total;for(const rr of MERC_RARITIES){roll-=rr.weight;if(roll<=0)return rr;}return MERC_RARITIES[0];}
function generateMercOffersForPlayer(p,force=false){
  const now=Date.now();let cat=mercCatalogs.get(p.id);
  if(!force&&cat&&cat.expires>now&&Array.isArray(cat.offers)&&cat.offers.length)return cat;
  const rng=makeRng(`${GALAXY_SEED}|merc|${p.memberId||p.id}|${Math.floor(now/MERC_OFFER_RESET_MS)}`);
  const offers=[];
  for(let i=0;i<MAX_MERC_OFFERS;i++){
    const rarity=pickMercRarity(rng),role=MERC_ROLES[Math.floor(rng()*MERC_ROLES.length)];
    const lv=Math.max(1,Math.floor((p.level||1)*(0.75+rng()*0.55)+i/5));
    const statLuck=0.92+rng()*0.22;
    const maxHp=Math.floor((role.baseHp+lv*6)*rarity.mult*statLuck);
    const maxShield=Math.floor((role.baseShield+lv*4)*rarity.mult*(0.9+rng()*0.25));
    const damage=Math.floor((role.baseDamage+lv*1.1)*rarity.mult*(0.92+rng()*0.22));
    const speed=Math.floor(role.baseSpeed*(0.92+rng()*0.18)*(rarity.key==="legendary"?1.08:1));
    const price=Math.floor((550+lv*185+maxHp*2+maxShield*2+damage*42)*rarity.mult);
    offers.push({id:`mo_${Math.floor(now/MERC_OFFER_RESET_MS)}_${i}_${Math.floor(rng()*999999)}`,name:`${MERC_NAME_A[Math.floor(rng()*MERC_NAME_A.length)]} ${MERC_NAME_B[Math.floor(rng()*MERC_NAME_B.length)]}`,role:role.key,roleName:role.name,rarity:rarity.key,rarityName:rarity.name,color:rarity.color,level:lv,maxHp,maxShield,damage,speed,price});
  }
  cat={expires:now+MERC_OFFER_RESET_MS-(now%MERC_OFFER_RESET_MS),offers};mercCatalogs.set(p.id,cat);return cat;
}
function publicMerc(m){return {id:m.id,name:m.name,role:m.role,roleName:m.roleName,rarity:m.rarity,rarityName:m.rarityName,color:m.color,level:m.level,hp:m.hp,maxHp:m.maxHp,shield:m.shield,maxShield:m.maxShield,damage:m.damage,speed:m.speed,x:m.x,y:m.y};}
function normalizeMercs(list,p){
  if(!Array.isArray(list))return [];
  return list.slice(0,MAX_ACTIVE_MERCS).map((m,i)=>({id:String(m.id||`merc_${Date.now()}_${i}`),name:safeText(m.name,32)||"Mercenary",role:String(m.role||"escort"),roleName:safeText(m.roleName,24)||"Escort",rarity:String(m.rarity||"common"),rarityName:safeText(m.rarityName,24)||"Common",color:safeText(m.color,16)||"#9db0c8",level:Math.max(1,Math.floor(Number(m.level)||1)),hp:Math.max(1,Math.floor(Number(m.hp)||m.maxHp||70)),maxHp:Math.max(1,Math.floor(Number(m.maxHp)||70)),shield:Math.max(0,Math.floor(Number(m.shield)||m.maxShield||35)),maxShield:Math.max(0,Math.floor(Number(m.maxShield)||35)),damage:Math.max(1,Math.floor(Number(m.damage)||10)),speed:Math.max(40,Math.floor(Number(m.speed)||100)),x:Number(m.x)||p.x,y:Number(m.y)||p.y,lastShotAt:0}));
}



/* ── Persistent planet maps ──
   These maps live on the server so one planet has one shared, mineable state.
   They reset only when the Railway process restarts. Persist to Wix/DB later for permanent worlds.
*/
const PLANET_TILE={EMPTY:0,DIRT:1,STONE:2,ORE1:3,ORE2:4,RARE:5,ICE:6,PACKED_ICE:7,LAVA:8,MAGMA:9,TOXIC_SLUDGE:10,SAND:11,SANDSTONE:12,GRASS:13,BEDROCK:14};
const BUILD_RESOURCE_TO_TILE={dirt:1,stone:2,ice_block:6,lava_rock:8,toxic_sludge:10,sand:11,grass_tuft:13};
const planetMaps=new Map();
function safePlanetInfo(raw){
  raw=raw||{};
  const type=(raw.type==="asteroid")?"asteroid":(["lush","desert","ice","toxic","volcanic","void_spawn","codex_neon","crystal_forest","storm","metallic","obsidian","miasma","charcoal","neon_reef","black_ice_world","ember_quartz_world","prism_moon","gloom_steel_world"].includes(raw.type)?raw.type:"lush");
  const resList=Array.isArray(raw.resList)?raw.resList.filter(k=>RES_KEYS.includes(k)).slice(0,12):["dirt","stone","copper","iron"];
  return {id:safeText(raw.id,80)||"planet",seed:safeText(raw.seed,100)||GALAXY_SEED,type,isAsteroid:!!raw.isAsteroid||type==="asteroid",resList,x:Math.round(Number(raw.x)||0),y:Math.round(Number(raw.y)||0),radius:Math.max(25,Math.min(280,Math.round(Number(raw.radius)||60)))};
}
function genPlanetMapServer(planet){
  if(planet?.isAsteroid||planet?.type==="asteroid"){
    const rngA=makeRng((planet.seed||planet.id)+"|asteroid-map"),randA=(a,b)=>Math.floor(rngA()*(b-a+1))+a,W=150,H=82,tiles=new Uint8Array(W*H),hp=new Uint8Array(W*H),heights=new Array(W).fill(H-6),idx=(x,y)=>y*W+x;
    const cx=W/2,cy=H/2,rx=W*.43,ry=H*.36;
    for(let y=0;y<H;y++)for(let x=0;x<W;x++){const nx=(x-cx)/rx,ny=(y-cy)/ry,edge=nx*nx+ny*ny+(rngA()-.5)*.10;if(edge<1){let t=2,th=58;if(edge>.78){t=12;th=42;}if(rngA()<.24){t=4;th=78;}if(rngA()<.14||edge<.32){t=5;th=100;}tiles[idx(x,y)]=t;hp[idx(x,y)]=th;}}
    for(let i=0;i<9;i++){let px=randA(18,W-18),py=randA(15,H-15);for(let s=0;s<46;s++){const rr=randA(2,4);for(let yy=-rr;yy<=rr;yy++)for(let xx=-rr;xx<=rr;xx++){const x=px+xx,y=py+yy;if(x>1&&y>1&&x<W-2&&y<H-3&&xx*xx+yy*yy<=rr*rr){tiles[idx(x,y)]=0;hp[idx(x,y)]=0;}}px=Math.max(4,Math.min(W-5,px+randA(-1,1)));py=Math.max(5,Math.min(H-5,py+randA(-1,1)));}}
    for(let y=H-3;y<H;y++)for(let x=0;x<W;x++){tiles[idx(x,y)]=PLANET_TILE.BEDROCK;hp[idx(x,y)]=255;}
    return {planet,W,H,tiles,hp,heights};
  }
  const rng=makeRng(planet.seed+"|map"),W=320,H=140,sy2=45+Math.floor(rng()*13)-6;
  const heights=new Array(W).fill(0).map((_,x)=>Math.floor(sy2+Math.sin((x/28)+rng()*10)*6+Math.sin((x/9)+rng()*10)*2+(rng()-0.5)*2));
  const tiles=new Uint8Array(W*H),hp=new Uint8Array(W*H),idx=(x,y)=>y*W+x;
  const tc={lush:{surface:13,shallow:1,deep:2,sHP:20,shHP:25,dHP:55},desert:{surface:11,shallow:11,deep:12,sHP:18,shHP:22,dHP:50},ice:{surface:6,shallow:6,deep:7,sHP:30,shHP:35,dHP:65},toxic:{surface:10,shallow:1,deep:2,sHP:22,shHP:28,dHP:60},volcanic:{surface:9,shallow:8,deep:2,sHP:40,shHP:50,dHP:70},void_spawn:{surface:10,shallow:2,deep:5,sHP:36,shHP:58,dHP:100},codex_neon:{surface:13,shallow:3,deep:5,sHP:24,shHP:58,dHP:95},crystal_forest:{surface:13,shallow:6,deep:5,sHP:24,shHP:45,dHP:90},storm:{surface:2,shallow:12,deep:4,sHP:32,shHP:54,dHP:82},metallic:{surface:2,shallow:12,deep:3,sHP:40,shHP:62,dHP:88},obsidian:{surface:2,shallow:14,deep:5,sHP:50,shHP:80,dHP:115},miasma:{surface:10,shallow:1,deep:5,sHP:34,shHP:60,dHP:105},charcoal:{surface:1,shallow:2,deep:4,sHP:24,shHP:44,dHP:76},neon_reef:{surface:13,shallow:3,deep:5,sHP:22,shHP:54,dHP:90},black_ice_world:{surface:6,shallow:7,deep:5,sHP:38,shHP:62,dHP:100},ember_quartz_world:{surface:8,shallow:9,deep:5,sHP:42,shHP:62,dHP:105},prism_moon:{surface:6,shallow:3,deep:5,sHP:30,shHP:58,dHP:96},gloom_steel_world:{surface:2,shallow:12,deep:4,sHP:46,shHP:70,dHP:106}};
  const cfg=tc[planet.type]||tc.lush;
  for(let x=0;x<W;x++){const h=Math.max(18,Math.min(H-10,heights[x]));for(let y=h;y<H;y++){let t=cfg.surface,th=cfg.sHP;if(y>h+8){t=cfg.shallow;th=cfg.shHP;}if(y>h+20&&rng()<0.35){t=cfg.deep;th=cfg.dHP;}if(y>h+35&&rng()<0.45){t=cfg.deep;th=cfg.dHP;}tiles[idx(x,y)]=t;hp[idx(x,y)]=th;}}
  const randInt2=(a,b)=>Math.floor(rng()*(b-a+1))+a;
  for(let i=0;i<7;i++){let cx2=randInt2(10,W-11),cy2=randInt2(35,H-20);const steps=randInt2(120,220);for(let s=0;s<steps;s++){const r=randInt2(2,4);for(let yy=-r;yy<=r;yy++)for(let xx=-r;xx<=r;xx++){const x=cx2+xx,y=cy2+yy;if(x>1&&y>1&&x<W-2&&y<H-5&&xx*xx+yy*yy<=r*r){tiles[idx(x,y)]=0;hp[idx(x,y)]=0;}}cx2+=randInt2(-1,1);cy2=Math.max(25,Math.min(H-10,cy2+randInt2(-1,1)));cx2=Math.max(2,Math.min(W-3,cx2));}}
  const pc=(t,count,minY)=>{for(let n=0;n<count;n++){const cx3=randInt2(10,W-11),cy3=randInt2(minY,H-10),rr=randInt2(3,8);for(let y=-rr;y<=rr;y++)for(let x=-rr;x<=rr;x++){if(x*x+y*y<=rr*rr){const px2=cx3+x,py2=cy3+y;if(px2>1&&py2>1&&px2<W-2&&py2<H-5){const id=idx(px2,py2);if(tiles[id]!==0){tiles[id]=t;hp[id]=t===5?95:70;}}}}}};
  pc(3,randInt2(10,16),55);pc(4,randInt2(8,14),65);pc(5,randInt2(3,6),85);
  for(let y=H-3;y<H;y++)for(let x=0;x<W;x++){tiles[idx(x,y)]=PLANET_TILE.BEDROCK;hp[idx(x,y)]=255;}
  return {planet,W,H,tiles,hp,heights};
}
function getPlanetMap(info){
  const planet=safePlanetInfo(info);
  let map=planetMaps.get(planet.id);
  if(!map){map=genPlanetMapServer(planet);planetMaps.set(planet.id,map);}
  return map;
}
function planetTileHash(planet,t,x,y){let h=2166136261;const seed=`${planet?.id||planet?.seed||"planet"}|${x}|${y}|${t}`;for(let i=0;i<seed.length;i++){h^=seed.charCodeAt(i);h=Math.imul(h,16777619);}return h>>>0;}
function planetResForTile(planet,t,x,y,H){
  const l=planet.resList&&planet.resList.length?planet.resList:["dirt","stone","copper","iron"];
  if(planet?.isAsteroid||planet?.type==="asteroid"){const pools={3:["iron","copper"],4:["crystal","gold"],5:["crystal","gold"]},pool=pools[t]||["stone"];return pool[planetTileHash(planet,t,x,y)%pool.length];}
  if(t===1)return"dirt";if(t===13)return"grass_tuft";if(t===11)return"sand";if(t===6)return"ice_block";if(t===7)return"black_ice";if(t===8)return"lava_rock";if(t===9)return"magma_core";if(t===10)return"toxic_sludge";if(t===2||t===12)return"stone";if(t===14)return"dark_obsidian";
  if([3,4,5].includes(t)){const min=t===5?5:t===4?4:3,candidates=l.filter(k=>(RES_RARITY[k]||1)>=min),pool=candidates.length?candidates:l;return pool[planetTileHash(planet,t,x,y)%pool.length]||"stone";}return"stone";
}
function hpForPlacedTile(tile){return ({1:22,2:55,6:30,8:45,10:28,11:18,13:20})[tile]||25;}



async function persistOfflineCreditGrant(memberId,pack,grantBase){
  memberId=String(memberId||"");
  if(!memberId||!WIX_PERSIST_URL||!WIX_PERSIST_SECRET)return {ok:false,error:"Player is offline and Wix persistence is not configured."};
  const loaded=await loadPersistedAccountSnapshot(memberId).catch(()=>null);
  const cached=accountLastGoodSnapshots.get(memberId);
  const base=loaded||cached||{memberId,displayName:"Space Eco Pilot",credits:300,maxSlots:24,invSlots:emptySlots(24),level:1,xp:0,shipType:"scout",attrs:{},badgeRewards:{},storyProgress:normalizeStoryProgress({}),equippedWeapon:"weapon_laser_mk1",weaponLevels:{weapon_laser_mk1:1},equippedAttachments:{},planetModules:defaultPlanetModules(),activeMercs:[],buildings:{},cosmeticInventory:{},equippedCosmetics:{},stationTierCosmetics:{},planetTypeCosmetics:{},redeemedCoupons:{},signupCreditBonusGranted:false};
  const payload={...base,memberId,credits:Math.max(0,Math.floor(Number(base.credits)||0))+pack.credits,reason:"offline_credit_purchase",updatedAt:Date.now()};
  const res=await fetch(WIX_PERSIST_URL,{method:"POST",headers:{"Content-Type":"application/json","Authorization":`Bearer ${WIX_PERSIST_SECRET}`},body:JSON.stringify(payload)});
  if(!res.ok){const text=await res.text().catch(()=>"");return {ok:false,error:`Wix persistence failed: ${res.status} ${text.slice(0,160)}`};}
  accountLastGoodSnapshots.set(memberId,{...payload,persistenceLoaded:true,savedGameReady:true});
  return {ok:true,grant:{...grantBase,memberId,creditsAdded:pack.credits,credits:payload.credits,offline:true,grantedAt:Date.now()}};
}

/* ── Credit purchase API called by Wix backend only ── */
app.get("/api/credit-packages", (_req,res)=>{
  res.json(Object.fromEntries(Object.entries(CREDIT_PACKAGES).map(([id,p])=>[id,{credits:p.credits,amount:p.amount,label:p.label}])));
});
app.post("/api/grant-credits", async (req,res)=>{
  if(!PURCHASE_WEBHOOK_SECRET){res.status(500).json({ok:false,error:"PURCHASE_WEBHOOK_SECRET is not configured on Railway."});return;}
  const auth=req.get("authorization")||"";
  if(auth!==`Bearer ${PURCHASE_WEBHOOK_SECRET}`){res.status(401).json({ok:false,error:"Unauthorized."});return;}
  const {paymentId,packageId,socketId,memberId}=req.body||{};
  if(!paymentId||!packageId||(!socketId&&!memberId)){res.status(400).json({ok:false,error:"paymentId, packageId, and socketId or memberId are required."});return;}
  const pack=CREDIT_PACKAGES[packageId];
  if(!pack){res.status(400).json({ok:false,error:"Unknown credit package."});return;}
  if(grantedCreditPayments.has(paymentId)){res.json({ok:true,duplicate:true,grant:grantedCreditPayments.get(paymentId)});return;}
  let p=socketId?players.get(String(socketId)):null;
  if(!p&&memberId){const sid=socketsByMemberId.get(String(memberId));if(sid)p=players.get(sid);}
  if(!p){
    const offline=await persistOfflineCreditGrant(memberId,pack,{paymentId,packageId,socketId:socketId||null,playerName:req.body?.playerName||"Space Eco Pilot"});
    if(!offline.ok){res.status(409).json({ok:false,error:offline.error||"Player socket is not online."});return;}
    grantedCreditPayments.set(paymentId,offline.grant);
    res.json({ok:true,grant:offline.grant});return;
  }
  p.credits=(p.credits||0)+pack.credits;
  const grant={paymentId,packageId,socketId:p.id,playerName:p.name,memberId:p.memberId||memberId||null,creditsAdded:pack.credits,credits:p.credits,grantedAt:Date.now()};
  grantedCreditPayments.set(paymentId,grant);
  addScore(p,Math.floor(pack.credits*0.002),"Credit Purchase");
  io.to(p.id).emit("creditPurchaseConfirm",grant);
  io.to(p.id).emit("creditUpdate",{credits:p.credits});
  syncAndPersist(p,"credit_purchase");
  res.json({ok:true,grant});
});

/* ── PvP projectiles ── */
const pvpProjectiles=[];
const planetProjectiles=[];
const SHOOT_CD=0.22, PROJ_SPEED=280, PROJ_LIFE=2.2, BASE_DAMAGE=18;
const PLANET_PROJ_SPEED=310, PLANET_PROJ_LIFE=1.55, PLANET_PROJ_HIT_RADIUS=12;

// Player shields may only recharge after the pilot has been out of combat for this long.
// This also prevents a depleted shield value of 0 from being mistaken for missing data.
const PLAYER_SHIELD_REGEN_DELAY = 3;
function markPlayerShieldCombat(p){
  if(!p)return;
  p.lastShieldHitAt = Date.now();
  const cur = Number.isFinite(Number(p.shieldRegenTimer)) ? Number(p.shieldRegenTimer) : 0;
  p.shieldRegenTimer = Math.max(cur, PLAYER_SHIELD_REGEN_DELAY);
}
function applyShieldHullDamageToPlayer(target, rawDamage, useArmor=true){
  if(!target||target.mode!=="space"||target.hp<=0)return {damage:0,hpDamage:0,shieldDamage:0,killed:false};
  const raw=Math.max(0,Math.min(220,Number(rawDamage)||0));
  if(raw<=0)return {damage:0,hpDamage:0,shieldDamage:0,killed:false};
  const armor=useArmor ? Math.max(0.2,1+((((target.attrs||{}).armor)||1)-1)*0.2) : 1;
  let dmg=raw/armor,shieldDamage=0,hpDamage=0;
  // Keep an actual 0 shield as 0. Never use `shield || maxShield` here.
  target.maxShield=Math.max(0,Number.isFinite(Number(target.maxShield))?Number(target.maxShield):0);
  target.shield=Math.max(0,Math.min(Number.isFinite(Number(target.shield))?Number(target.shield):0,target.maxShield));
  if(target.shield>0){
    shieldDamage=Math.min(target.shield,dmg);
    target.shield=Math.max(0,target.shield-shieldDamage);
    dmg-=shieldDamage;
  }
  if(dmg>0){
    target.hp=Math.max(0,Math.min(Number.isFinite(Number(target.hp))?Number(target.hp):0,Number.isFinite(Number(target.maxHp))?Number(target.maxHp):999999));
    hpDamage=Math.min(target.hp,dmg);
    target.hp=Math.max(0,target.hp-hpDamage);
  }
  markPlayerShieldCombat(target);
  return {damage:Math.round(raw/armor),hpDamage,shieldDamage,killed:target.hp<=0};
}

function pointSegmentDistance(px,py,ax,ay,bx,by){
  const abx=bx-ax,aby=by-ay,apx=px-ax,apy=py-ay;
  const ab2=abx*abx+aby*aby;
  const t=ab2>0?Math.max(0,Math.min(1,(apx*abx+apy*aby)/ab2)):0;
  const cx=ax+abx*t,cy=ay+aby*t;
  return Math.hypot(px-cx,py-cy);
}
function shipHitRadiusFor(p){
  const size=(SHIP_TYPES[p?.shipType||"scout"]||SHIP_TYPES.scout).size;
  return size==="huge"?24:size==="large"?20:size==="medium"?17:15;
}
function tickProjectiles(dt){
  for(let i=pvpProjectiles.length-1;i>=0;i--){
    const p=pvpProjectiles[i];
    const ox=Number.isFinite(Number(p.x))?p.x:(p.prevX||0),oy=Number.isFinite(Number(p.y))?p.y:(p.prevY||0);
    p.prevX=ox;p.prevY=oy;p.x+=p.vx*dt;p.y+=p.vy*dt;p.life-=dt;
    if(p.life<=0){pvpProjectiles.splice(i,1);continue;}
    let consumed=false;
    for(const[sid,target]of players){
      if(sid===p.ownerId||target.mode!=="space"||target.hp<=0)continue;
      const owner=players.get(p.ownerId);
      if(areAllied(owner,target))continue;
      const hitRadius=shipHitRadiusFor(target)+(Number(p.size)||2.5);
      if(pointSegmentDistance(target.x,target.y,ox,oy,p.x,p.y)<=hitRadius){
        const result=applyShieldHullDamageToPlayer(target,p.damage,true);
        io.to(sid).emit("hit",{damage:result.damage,hp:target.hp,shield:target.shield,by:p.ownerId});
        if(p.ownerId)io.to(p.ownerId).emit("hitConfirm",{targetId:sid,damage:result.damage,weaponKey:p.weaponKey,color:p.color});
        pvpProjectiles.splice(i,1);consumed=true;
        if(result.killed)handlePlayerKill(sid,p.ownerId);
        break;
      }
    }
    if(consumed)continue;
  }
}

function killPlayerOnPlanet(victim, killer, killerName){
  if(!victim)return;
  victim.deaths=(victim.deaths||0)+1;
  if(killer){killer.kills=(killer.kills||0)+1;killer.credits+=75;addScore(killer,250,"Planet PvP");io.to(killer.id).emit("creditUpdate",{credits:killer.credits});}
  io.to(victim.id).emit("youDied",{killedBy:killerName||killer?.name||"Planet combat"});
  io.emit("playerKilled",{victimId:victim.id,victimName:victim.name,killerId:killer?.id||null,killerName:killerName||killer?.name||"Planet combat"});
  setTimeout(()=>{
    const rp=players.get(victim.id);if(!rp)return;
    if(rp.planetId)io.sockets.sockets.get(rp.id)?.leave(`planet:${rp.planetId}`);
    const sp=computeSpawnPoint();rp.mode="space";rp.planetId=null;refreshPlanetSuitStats(rp);rp.x=sp.x;rp.y=sp.y;rp.hp=rp.maxHp;rp.shield=rp.maxShield;rp.energy=100;rp.planetX=0;rp.planetY=0;
    io.to(rp.id).emit("respawn",{x:rp.x,y:rp.y});
  },3000);
  broadcastLeaderboard();
}

function tickPlanetProjectiles(dt){
  for(let i=planetProjectiles.length-1;i>=0;i--){
    const pr=planetProjectiles[i];pr.x+=pr.vx*dt;pr.y+=pr.vy*dt;pr.life-=dt;
    if(pr.life<=0){planetProjectiles.splice(i,1);continue;}
    const map=planetMaps.get(pr.planetId);
    if(map){const tx=Math.floor(pr.x/16),ty=Math.floor(pr.y/16);if(tx<0||ty<0||tx>=map.W||ty>=map.H){planetProjectiles.splice(i,1);continue;}if(map.tiles[ty*map.W+tx]){planetProjectiles.splice(i,1);continue;}}
    for(const [,target] of players){
      if(target.id===pr.ownerId||target.mode!=="planet"||target.planetId!==pr.planetId||target.hp<=0)continue;
      if(areAllied(players.get(pr.ownerId),target))continue;
      const d=Math.hypot((target.planetX||0)-pr.x,((target.planetY||0)-8)-pr.y);
      if(d<PLANET_PROJ_HIT_RADIUS){
        const owner=players.get(pr.ownerId);
        const armor=1+((target.attrs.armor-1)*0.08),dmg=planetDamageAfterModules(target,pr.damage/armor);
        target.hp=Math.max(0,target.hp-dmg);target.lastPlanetAttacker=pr.ownerId;
        io.to(pr.ownerId).emit("planetAttackConfirm",{targetId:target.id,damage:Math.round(dmg),hp:target.hp});
        io.to(target.id).emit("planetHit",{damage:Math.round(dmg),hp:target.hp,attackerName:pr.ownerName});
        planetProjectiles.splice(i,1);
        if(target.hp<=0)killPlayerOnPlanet(target,owner,pr.ownerName);
        break;
      }
    }
  }
}

function handlePlayerKill(victimId, killerId){
  const victim=players.get(victimId),killer=players.get(killerId);
  if(!victim)return;
  victim.deaths=(victim.deaths||0)+1;
  io.to(victimId).emit("youDied",{killedBy:killer?killer.name:"Unknown"});
  if(killer){
    killer.kills=(killer.kills||0)+1;killer.credits+=150;
    addScore(killer,500,"PvP Kill");
    io.to(killerId).emit("killConfirm",{name:victim.name});
    io.to(killerId).emit("creditUpdate",{credits:killer.credits});
  }
  io.emit("playerKilled",{victimId,victimName:victim.name,killerId,killerName:killer?.name});
  broadcastLeaderboard();
  scheduleRespawnForPlayer(victim,"pvp-kill",2500);
}

function applySpaceDamageToPlayer(target, rawDamage, attacker, sourceName="Ally Trade Ship"){
  const result=applyShieldHullDamageToPlayer(target,rawDamage,true);
  if(result.damage<=0)return {damage:0,killed:false};
  io.to(target.id).emit("hit",{damage:result.damage,hp:target.hp,shield:target.shield,by:attacker?.id||sourceName,source:sourceName});
  if(attacker?.id)io.to(attacker.id).emit("hitConfirm",{targetId:target.id,damage:result.damage,source:sourceName});
  if(result.killed)handlePlayerKill(target.id,attacker?.id||null);
  return {damage:result.damage,killed:result.killed};
}

function forceRespawnPlayer(p,reason="respawn"){
  if(!p)return null;
  try{if(p.planetId)io.sockets.sockets.get(p.id)?.leave(`planet:${p.planetId}`);}catch(_){/* noop */}
  const sp=computeSpawnPoint();
  p.mode="space";p.planetId=null;refreshPlanetSuitStats(p);p.x=sp.x;p.y=sp.y;p.vx=0;p.vy=0;p.angle=0;
  p.planetX=0;p.planetY=0;p.planetVx=0;p.planetVy=0;p.planetTool="mining";
  p.hp=Number.isFinite(Number(p.maxHp))?Number(p.maxHp):100;
  p.shield=Number.isFinite(Number(p.maxShield))?Number(p.maxShield):0;
  p.energy=100;p.shieldRegenTimer=0;p.dead=false;p.respawnPending=false;p.respawnAt=0;
  io.to(p.id).emit("respawn",{x:p.x,y:p.y,reason});
  return p;
}
function scheduleRespawnForPlayer(p,reason="death",delay=3000){
  if(!p||p.respawnPending)return;
  p.dead=true;p.respawnPending=true;p.respawnAt=Date.now()+Math.max(250,Math.floor(Number(delay)||3000));p.hp=0;
  setTimeout(()=>{const rp=players.get(p.id);if(!rp)return;forceRespawnPlayer(rp,reason);},Math.max(250,Math.floor(Number(delay)||3000)));
}
function tickRespawnFailsafes(){
  const now=Date.now();
  for(const p of players.values()){
    if((Number(p.hp)||0)<=0&&!p.respawnPending)scheduleRespawnForPlayer(p,"failsafe",2500);
    else if(p.respawnPending&&(now-(p.respawnAt||now)>12000))forceRespawnPlayer(p,"failsafe-force");
  }
}

/* ── Physics tick ── */
const ROT_SPEED=2.25, BASE_THRUST=104, BASE_MAX_VELOCITY=165, ENERGY_DRAIN=1.8, ENERGY_IDLE=0.15, GAS_REFUEL=30;

function tickPlayers(dt){
  for(const[,p]of players){
    if(p.mode!=="space")continue;
    const ship=SHIP_TYPES[p.shipType]||SHIP_TYPES.scout;
    const fx=applyShipStats(p,false);
    const speedStat=(1+((p.attrs.speed-1)*0.3))*ship.thrustMult*fx.thrustMult;
    const brakingStat=(1+(((p.attrs.braking||1)-1)*0.22))*Math.max(0.35,(ship.brakingMult||1))*fx.brakingMult;
    const turnStat=Math.max(0.55,(ship.turnMult||1))*fx.turnMult;
    const gasEff=(1/Math.max(0.3,1+((p.attrs.gasEfficiency-1)*0.15)))/Math.max(0.35,fx.gasEfficiencyMult);
    const shRegen=3*(1+((p.attrs.shieldRegen-1)*0.4))*ship.shieldRegenMult*fx.shieldRegenMult;
    const inp=p.input;
    if(inp.rotLeft)p.angle-=ROT_SPEED*turnStat*dt;
    if(inp.rotRight)p.angle+=ROT_SPEED*turnStat*dt;
    if(inp.thrust){p.vx+=Math.cos(p.angle)*BASE_THRUST*speedStat*dt;p.vy+=Math.sin(p.angle)*BASE_THRUST*speedStat*dt;p.energy=Math.max(0,p.energy-ENERGY_DRAIN*gasEff*dt);}
    else if(Math.hypot(p.vx,p.vy)>5)p.energy=Math.max(0,p.energy-ENERGY_IDLE*gasEff*dt);
    if(inp.brake){const brakeDrag=Math.pow(Math.max(0.74,0.925-(brakingStat-1)*0.035),dt*60);p.vx*=brakeDrag;p.vy*=brakeDrag;}
    const drag=Math.pow(0.995,dt*60);p.vx*=drag;p.vy*=drag;
    const maxVel=BASE_MAX_VELOCITY*Math.max(0.55,Math.min(1.32,speedStat));
    const curVel=Math.hypot(p.vx,p.vy);
    if(curVel>maxVel){const s=maxVel/curVel;p.vx*=s;p.vy*=s;}
    p.x+=p.vx*dt;p.y+=p.vy*dt;
    // Shield recharge is strictly delayed until the player has been out of combat.
    p.shieldRegenTimer=Math.max(0,(Number(p.shieldRegenTimer)||0)-dt);
    p.shield=Math.max(0,Math.min(Number.isFinite(Number(p.shield))?Number(p.shield):0,p.maxShield));
    if(p.shieldRegenTimer<=0&&p.shield<p.maxShield)p.shield=Math.min(p.maxShield,p.shield+shRegen*dt);
    if(inp.shootX!==null&&p.shootCooldown<=0&&p.hp>0){
      const ang=Math.atan2(inp.shootY-p.y,inp.shootX-p.x);
      const dmgStat=(1+((p.attrs.damage-1)*0.4))*ship.damageMult*fx.damageMult;
      p.shootCooldown=spawnWeaponProjectiles(p,ang,dmgStat);inp.shootX=null;inp.shootY=null;
    }
    if(p.shootCooldown>0)p.shootCooldown=Math.max(0,p.shootCooldown-dt);
    p.lastSeen=Date.now();
  }
}

/* ── Broadcast ── */
function snap(p){return{id:p.id,name:p.name,x:p.x,y:p.y,vx:p.vx,vy:p.vy,angle:p.angle,hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield,shieldRegenTimer:p.shieldRegenTimer||0,color:p.color,level:p.level,mode:p.mode,score:p.score||0,kills:p.kills||0,shipType:p.shipType||"scout",ping:p.ping||0,planetId:p.planetId,planetX:p.planetX||0,planetY:p.planetY||0,cosmeticColor:p.cosmeticColor,suitColor:p.suitColor,weaponLevel:p.weaponLevel||1,equippedWeapon:p.equippedWeapon||"weapon_laser_mk1",equippedAttachments:normalizeAttachments(p.equippedAttachments||{}),equippedCosmetics:normalizeEquippedCosmetics(p.equippedCosmetics||{})};}
function serverListSnap(p){return{id:p.id,name:p.name,x:Math.round(p.x),y:Math.round(p.y),level:p.level,score:p.score||0,kills:p.kills||0,deaths:p.deaths||0,shipType:p.shipType||"scout",ping:p.ping||0,mode:p.mode,partyId:p.partyId||null,factionId:p.factionId||null,factionTag:factionTagFor(p.factionId)};}

function broadcastWorldState(){
  const all=[ ...players.values()].map(snap);
  const projs=pvpProjectiles.map(p=>({id:p.id,x:p.x,y:p.y,vx:p.vx,vy:p.vy,ownerId:p.ownerId,weaponKey:p.weaponKey,color:p.color,size:p.size,mode:p.mode,life:p.life}));
  for(const[sid,p]of players){
    const nearby=all.filter(s=>s.id!==sid&&Math.hypot(s.x-p.x,s.y-p.y)<BROADCAST_RANGE);
    const nearProj=projs.filter(pr=>Math.hypot(pr.x-p.x,pr.y-p.y)<BROADCAST_RANGE);
    io.to(sid).emit("worldState",{self:snap(p),others:nearby,pvpProjectiles:nearProj});
    if(p.mode==="planet"&&p.planetId){
      const pps=[...players.values()].filter(o=>o.id!==sid&&o.mode==="planet"&&o.planetId===p.planetId).map(o=>({id:o.id,name:o.name,x:o.planetX||0,y:o.planetY||0,vx:o.planetVx||0,vy:o.planetVy||0,hp:o.hp,maxHp:o.maxHp,color:o.color,level:o.level,cosmeticColor:o.cosmeticColor,suitColor:o.suitColor,tool:o.planetTool||"mining",weaponLevel:o.weaponLevel||1,equippedCosmetics:normalizeEquippedCosmetics(o.equippedCosmetics||{})}));
      const pprs=planetProjectiles.filter(pr=>pr.planetId===p.planetId).map(pr=>({id:pr.id,ownerId:pr.ownerId,x:pr.x,y:pr.y,vx:pr.vx,vy:pr.vy}));
      io.to(sid).emit("planetPlayersState",{planetId:p.planetId,players:pps,projectiles:pprs});
    }
  }
}

function broadcastLeaderboard(){io.emit("leaderboard",buildLeaderboard(10));}
function broadcastServerList(){io.emit("serverList",{name:SERVER_NAME,players:[...players.values()].map(serverListSnap),uptime:Math.floor((Date.now()-SERVER_START)/1000)});}
function broadcastChat(from,message,color){io.emit("chat",{from,message:String(message).replace(/</g,"&lt;").slice(0,120),color:color||"#d6e1ff",ts:Date.now()});}

/* ── Owned stations ── */
const ownedStations=new Map();
const stationHazardDamageCooldowns=new Map();

function ownedStationListFor(socketId){
  return [...ownedStations.values()].map(st=>({
    key:st.key,
    x:st.x,
    y:st.y,
    tier:st.tier,
    ownerName:st.ownerName,
    shipCount:st.hiredShips.filter(sh=>sh.state!=="respawning").length,
    ships:st.hiredShips.map(sh=>({id:sh.id,state:sh.state||"collecting",respawnAt:sh.respawnAt||0})),
    hp:Math.round(st.hp||0),
    maxHp:st.maxHp||stationDefenseStats(st.tier).maxHp,
    shield:Math.round(st.shield||0),
    maxShield:st.maxShield||stationDefenseStats(st.tier).maxShield,
    destroyed:!!st.destroyed,
    underAttackUntil:st.underAttackUntil||0,
    goodsCount:Object.values(st.accumulatedGoods||{}).reduce((a,b)=>a+b,0),
    isOwn:st.ownerId===socketId
  }));
}
function emitOwnedStationsList(socket){
  socket.emit("ownedStationsList",ownedStationListFor(socket.id));
}
function broadcastOwnedStationsList(){
  for(const [,s] of io.sockets.sockets)emitOwnedStationsList(s);
}

setInterval(()=>{
  const RESOURCES=["stone","copper","iron","gold","crystal","lava_rock","ice_block"];
  for(const[,st]of ownedStations){
    if(st.destroyed||st.hiredShips.length===0)continue;
    for(const ship of st.hiredShips){
      if(ship.state==="respawning")continue;
      const count=2+Math.floor(Math.random()*6);
      for(let i=0;i<count;i++){const r=RESOURCES[Math.floor(Math.random()*RESOURCES.length)];st.accumulatedGoods[r]=(st.accumulatedGoods[r]||0)+1;}
    }
    const owner=players.get(st.ownerId);
    if(owner)io.to(st.ownerId).emit("ownedStationUpdate",{stationKey:st.key,goodsCount:Object.values(st.accumulatedGoods).reduce((a,b)=>a+b,0),shipCount:st.hiredShips.filter(sh=>sh.state!=="respawning").length});
  }
},30000);

setInterval(tickCivilizationTaxes,60000);
setInterval(tickCivilizationLogistics,CIV_LOGISTICS_TICK_MS);

/* ── Main tick ── */
let lastTick=Date.now(),ecoTimer=0,lbTimer=0,slTimer=0,socialTimer=0;
setInterval(()=>{
  const now=Date.now(),dt=Math.min((now-lastTick)/1000,0.05);lastTick=now;
  economy.tick();tickPlayers(dt);tickProjectiles(dt);tickPlanetProjectiles(dt);tickOwnedStationDefense(dt);tickPlayerStructures(dt);tickRespawnFailsafes();broadcastWorldState();
  ecoTimer+=dt;if(ecoTimer>=5){io.emit("economyUpdate",economy.snapshot());ecoTimer=0;}
  lbTimer+=dt; if(lbTimer>=10){broadcastLeaderboard();lbTimer=0;}
  slTimer+=dt; if(slTimer>=3){broadcastServerList();broadcastOwnedStationsList();broadcastCivilizationZonesList();slTimer=0;}
  socialTimer+=dt; if(socialTimer>=2){for(const id of parties.keys())emitPartyState(id);for(const id of factions.keys())emitFactionState(id);socialTimer=0;}
},TICK_MS);


/* ── Player-to-player trade sessions ── */
const tradeSessions=new Map();
let tradeSeq=1;
function blankTradeOffer(){return {credits:0,items:[]};}
function sanitizeTradeOffer(offer,player){
  const out=blankTradeOffer();
  out.credits=Math.max(0,Math.min(Math.floor(Number(offer?.credits)||0),Math.max(0,player.credits||0)));
  const seen=new Map();
  for(const it of (offer?.items||[])){
    const type=String(it.type||"");
    if(!isInventoryItemKey(type))continue;
    const q=Math.max(0,Math.min(999,Math.floor(Number(it.quantity)||0)));
    if(q>0)seen.set(type,(seen.get(type)||0)+q);
  }
  out.items=[...seen.entries()].map(([type,quantity])=>({type,quantity})).slice(0,12);
  return out;
}
function tradeOfferKey(offer){
  const credits=Math.max(0,Math.floor(Number(offer?.credits)||0));
  const items=(offer?.items||[])
    .map(it=>({type:String(it.type||""),quantity:Math.max(0,Math.floor(Number(it.quantity)||0))}))
    .filter(it=>isInventoryItemKey(it.type)&&it.quantity>0)
    .sort((a,b)=>a.type.localeCompare(b.type));
  return `${credits}|${items.map(it=>`${it.type}:${it.quantity}`).join(",")}`;
}
function tradeOffersEqual(a,b){return tradeOfferKey(a)===tradeOfferKey(b);}
function cloneTradeInventory(p){
  const maxSlots=Math.max(24,Math.min(96,Math.floor(Number(p?.maxSlots)||24)));
  const src=Array.isArray(p?.invSlots)?p.invSlots:emptySlots(maxSlots);
  const invSlots=emptySlots(maxSlots);
  for(let i=0;i<Math.min(src.length,maxSlots);i++){
    const type=String(src[i]?.type||"");
    const count=Math.max(0,Math.floor(Number(src[i]?.count)||0));
    invSlots[i]=(type&&isInventoryItemKey(type)&&count>0)?{type,count}:{type:null,count:0};
  }
  return {maxSlots,invSlots};
}
function simulateTradeInventory(player,giveOffer,receiveOffer){
  const sim=cloneTradeInventory(player);
  for(const it of giveOffer.items||[]){
    if(!removeInventory(sim,it.type,it.quantity))return {ok:false,reason:"offered items are no longer available"};
  }
  for(const it of receiveOffer.items||[]){
    if(!addInventory(sim,it.type,it.quantity))return {ok:false,reason:"not enough inventory space to receive the trade"};
  }
  return {ok:true,invSlots:sim.invSlots,maxSlots:sim.maxSlots};
}
function sideOfTrade(s,id){return s?.a===id?"a":s?.b===id?"b":null;}
function emitTradeState(s){
  if(!s)return;
  const pa=players.get(s.a),pb=players.get(s.b);if(!pa||!pb)return;
  const base={tradeId:s.id,players:{a:s.a,b:s.b},names:{a:pa.name,b:pb.name},offers:s.offers,ready:s.ready};
  io.to(s.a).emit("tradeSessionState",{...base,yourSide:"a",otherId:s.b,otherName:pb.name});
  io.to(s.b).emit("tradeSessionState",{...base,yourSide:"b",otherId:s.a,otherName:pa.name});
}
function startTrade(aId,bId){
  const pa=players.get(aId),pb=players.get(bId);if(!pa||!pb)return null;
  const id=`tr_${Date.now()}_${tradeSeq++}`;
  const s={id,a:aId,b:bId,offers:{a:blankTradeOffer(),b:blankTradeOffer()},ready:{a:false,b:false},createdAt:Date.now()};
  tradeSessions.set(id,s);
  const base={tradeId:s.id,players:{a:s.a,b:s.b},names:{a:pa.name,b:pb.name},offers:s.offers,ready:s.ready};
  io.to(s.a).emit("tradeStarted",{...base,yourSide:"a",otherId:s.b,otherName:pb.name});
  io.to(s.b).emit("tradeStarted",{...base,yourSide:"b",otherId:s.a,otherName:pa.name});
  return s;
}
function cancelTrade(s,reason="Trade cancelled."){
  if(!s)return;tradeSessions.delete(s.id);
  io.to(s.a).emit("tradeCancelled",{tradeId:s.id,reason});
  io.to(s.b).emit("tradeCancelled",{tradeId:s.id,reason});
}
function completeTrade(s){
  const pa=players.get(s.a),pb=players.get(s.b);if(!pa||!pb){cancelTrade(s,"Trade cancelled: player disconnected.");return;}
  const oa=sanitizeTradeOffer(s.offers.a,pa),ob=sanitizeTradeOffer(s.offers.b,pb);
  s.offers.a=oa;s.offers.b=ob;
  if((pa.credits||0)<(oa.credits||0)||(pb.credits||0)<(ob.credits||0)){cancelTrade(s,"Trade cancelled: insufficient credits.");return;}
  if(!validateTradeItems(pa,oa.items)||!validateTradeItems(pb,ob.items)){cancelTrade(s,"Trade cancelled: one player no longer has the offered inventory.");return;}
  const simA=simulateTradeInventory(pa,oa,ob),simB=simulateTradeInventory(pb,ob,oa);
  if(!simA.ok){cancelTrade(s,`Trade cancelled: ${pa.name} has ${simA.reason}.`);return;}
  if(!simB.ok){cancelTrade(s,`Trade cancelled: ${pb.name} has ${simB.reason}.`);return;}
  // Commit the simulated inventories atomically so no partial add/remove can occur.
  pa.invSlots=normalizeInventorySlots(simA.invSlots,pa.maxSlots||24);
  pb.invSlots=normalizeInventorySlots(simB.invSlots,pb.maxSlots||24);
  pa.credits=(pa.credits||0)-(oa.credits||0)+(ob.credits||0);
  pb.credits=(pb.credits||0)-(ob.credits||0)+(oa.credits||0);
  tradeSessions.delete(s.id);
  syncAndPersist(pa,"trade_complete");syncAndPersist(pb,"trade_complete");
  io.to(pa.id).emit("tradeComplete",{tradeId:s.id,credits:pa.credits,invSlots:pa.invSlots,maxSlots:pa.maxSlots,gaveOffer:oa,receivedOffer:ob,otherName:pb.name,serverAuthoritative:true});
  io.to(pb.id).emit("tradeComplete",{tradeId:s.id,credits:pb.credits,invSlots:pb.invSlots,maxSlots:pb.maxSlots,gaveOffer:ob,receivedOffer:oa,otherName:pa.name,serverAuthoritative:true});
}


/* ── Party + faction system ── */
const parties = new Map();
const factions = new Map();
let partySeq = 1, factionSeq = 1;
const FACTION_CREATE_COST = 5000;
const PARTY_MAX_MEMBERS = 8;
const FACTION_QUEST_BASE_RESET_MS = 10*60*1000;
const FACTION_QUEST_MIN_RESET_MS = 2*60*1000;
function factionQuestResetMs(level=1){
  // Level 1 factions refresh every 10 minutes; veteran factions cycle faster, down to 2 minutes.
  return Math.max(FACTION_QUEST_MIN_RESET_MS, Math.floor(FACTION_QUEST_BASE_RESET_MS / (1 + Math.max(0,level-1)*0.18)));
}

function safeText(v,max=80){return String(v||"").replace(/[<>]/g,"").trim().slice(0,max);}
function factionTagFor(id){const f=id?factions.get(id):null;return f?f.tag:null;}
function factionCapacity(f){return 15 + Math.max(0,(f?.level||1)-1)*5;}
function factionXpNeeded(level){return Math.floor(2500*Math.pow(Math.max(1,level),1.35));}
function makePartyState(partyId){const party=parties.get(partyId);if(!party)return null;const members=[...party.members].map(id=>{const p=players.get(id);return p?{id:p.id,name:p.name,leader:id===party.leaderId,mode:p.mode,x:Math.round(p.x||0),y:Math.round(p.y||0),planetId:p.planetId||null,planetX:Math.round(p.planetX||0),planetY:Math.round(p.planetY||0),hp:Math.round(p.hp||0),maxHp:p.maxHp||100,shipType:p.shipType||"scout",online:true}:null;}).filter(Boolean);return {id:party.id,leaderId:party.leaderId,members,maxMembers:PARTY_MAX_MEMBERS};}
function emitPartyState(partyId){const st=makePartyState(partyId);if(!st)return;for(const m of st.members)io.to(m.id).emit("partyState",st);}
function leaveParty(playerId,reason="left the party"){
  const p=players.get(playerId);if(!p?.partyId)return;
  const party=parties.get(p.partyId);if(!party){p.partyId=null;return;}
  party.members.delete(playerId);p.partyId=null;io.to(playerId).emit("partyLeft",{reason});
  if(party.members.size===0){parties.delete(party.id);return;}
  if(party.leaderId===playerId)party.leaderId=[...party.members][0];
  emitPartyState(party.id);
}
function nearbyForInvite(a,b){if(!a||!b)return false;if(a.mode==="planet"&&b.mode==="planet"&&a.planetId===b.planetId)return Math.hypot((a.planetX||0)-(b.planetX||0),(a.planetY||0)-(b.planetY||0))<140;if(a.mode==="space"&&b.mode==="space")return Math.hypot((a.x||0)-(b.x||0),(a.y||0)-(b.y||0))<300;return false;}
function getOrCreatePartyForLeader(p){if(p.partyId)return parties.get(p.partyId);const id=`party_${Date.now()}_${partySeq++}`;const party={id,leaderId:p.id,members:new Set([p.id]),invites:new Map(),createdAt:Date.now()};parties.set(id,party);p.partyId=id;emitPartyState(id);return party;}
function areAllied(a,b){if(!a||!b)return false;if(a.id===b.id)return true;if(a.partyId&&a.partyId===b.partyId)return true;if(a.factionId&&a.factionId===b.factionId)return true;return false;}
function makeFactionQuests(f){
  const level=Math.max(1,f.level||1);
  const count=Math.min(8,3+Math.floor(level/2));
  const quests=[];
  const titles=["Mine Resonant Ore","Secure Trade Routes","Chart Planet Worksites","Train Combat Wing","Deliver Guild XP","Break Pirate Pressure","Fortify Guild Supply","Survey Deep Space"];
  for(let i=0;i<count;i++){
    const diff=level+i;
    const target=Math.floor(1200*Math.pow(1.28,level-1) + diff*520 + i*360);
    quests.push({
      id:`fq_${f.id}_${Date.now()}_${i}`,
      title:titles[i%titles.length],
      description:`Earn ${target} XP while this quest is accepted. Only one member can complete it.`,
      type:"earn_xp",target,progress:0,acceptedBy:null,acceptedByName:null,completed:false,
      rewardPlayerXp:Math.floor(target*1.15),
      rewardFactionXp:Math.floor(target*4.0),
      rewardCredits:Math.floor(600 + target*0.35 + level*125)
    });
  }
  f.quests=quests;
  f.questResetAt=Date.now()+factionQuestResetMs(level);
}
function ensureFactionQuests(f){if(!f)return;if(!f.quests||Date.now()>(f.questResetAt||0))makeFactionQuests(f);}
function makeFactionState(factionId,forPlayerId=null){const f=factions.get(factionId);if(!f)return null;ensureFactionQuests(f);const members=[...f.members].map(id=>{const p=players.get(id);const meta=f.memberMeta[id]||{};return {id,name:p?.name||meta.name||"Pilot",online:!!p,role:meta.role||"member",rank:meta.rank||"Member",contribution:meta.contribution||0,level:p?.level||meta.level||1,mode:p?.mode||"offline",x:Math.round(p?.x||0),y:Math.round(p?.y||0),planetId:p?.planetId||null};});return {id:f.id,name:f.name,tag:f.tag,icon:f.icon,color:f.color,description:f.description,leaderId:f.leaderId,level:f.level,xp:f.xp,xpNeeded:factionXpNeeded(f.level),capacity:factionCapacity(f),members,quests:f.quests,questResetAt:f.questResetAt,yourRole:f.memberMeta[forPlayerId]?.role||null};}
function emitFactionState(factionId){const f=factions.get(factionId);if(!f)return;for(const id of f.members)io.to(id).emit("factionState",makeFactionState(factionId,id));}
function playerFactionRole(f,id){return f?.memberMeta?.[id]?.role||"member";}
function canManageFaction(f,id){const r=playerFactionRole(f,id);return f?.leaderId===id||r==="leader"||r==="admin";}
function contributeFactionXp(p,amount,reason="XP"){
  if(!p?.factionId)return;const f=factions.get(p.factionId);if(!f)return;ensureFactionQuests(f);
  const gain=Math.max(1,Math.floor(Number(amount)||0));
  f.xp=(f.xp||0)+gain;
  (f.memberMeta[p.id]||(f.memberMeta[p.id]={name:p.name,role:"member",rank:"Member",contribution:0})).contribution+=gain;
  p.factionContribution=(p.factionContribution||0)+gain;
  while(f.xp>=factionXpNeeded(f.level)){f.xp-=factionXpNeeded(f.level);f.level++;broadcastChat("Faction",`${f.name} reached faction level ${f.level}!`,f.color||"#ffdd44");makeFactionQuests(f);}
  const q=(f.quests||[]).find(q=>q.acceptedBy===p.id&&!q.completed);
  if(q&&q.type==="earn_xp"){
    q.progress=Math.min(q.target,(q.progress||0)+gain);
    if(q.progress>=q.target){
      q.completed=true;
      p.activeFactionQuestId=null;
      f.xp=(f.xp||0)+(q.rewardFactionXp||0);
      while(f.xp>=factionXpNeeded(f.level)){f.xp-=factionXpNeeded(f.level);f.level++;broadcastChat("Faction",`${f.name} reached faction level ${f.level}!`,f.color||"#ffdd44");makeFactionQuests(f);}
      const rewardCredits=Math.max(0,Math.floor(Number(q.rewardCredits)||0));
      if(rewardCredits>0){p.credits=(p.credits||0)+rewardCredits;io.to(p.id).emit("creditUpdate",{credits:p.credits});}
      addPlayerXpOnly(p,q.rewardPlayerXp||0,"Faction Quest Reward");
      io.to(p.id).emit("factionQuestCompleted",{questId:q.id,rewardPlayerXp:q.rewardPlayerXp,rewardFactionXp:q.rewardFactionXp,rewardCredits});
      persistPlayerSoon(p,"faction_quest_complete");
    }
  }
  emitFactionState(f.id);
}

/* ── Socket events ── */
io.on("connection",socket=>{
  if(players.size>=MAX_PLAYERS){socket.emit("serverFull");socket.disconnect(true);return;}

  socket.on("join",async (joinPayload={})=>{
    if(players.has(socket.id))return;
    const {name,token,wixSnapshot,resumeToken}=joinPayload||{};
    let auth=combineAuthWithClientSnapshot(verifyGameToken(token),wixSnapshot);
    auth=await enrichAuthWithPersistedSnapshot(auth,"join");
    if(players.has(socket.id)||!socket.connected)return;
    const resumed=takeTransientReconnectSession(resumeToken,auth);
    let p;
    if(resumed){
      p=resumed.player;
      rebindTransientPlayerSession(p,resumed.oldId,socket.id,auth?.displayName||name||p.name);
      // A guest can sign in while the reconnect is happening.  Existing
      // member sessions keep their authoritative in-memory state instead of
      // being overwritten by a delayed browser snapshot.
      if(auth&&!p.memberId)applyAuthAccountToPlayer(p,auth);
    }else{
      const sp=computeSpawnPoint();p=defaultPlayer(socket.id,auth?.displayName||name,sp.x,sp.y);
      applyAuthAccountToPlayer(p,auth);
    }
    p.connectionResumeToken=normalizeReconnectToken(resumeToken)||p.connectionResumeToken||"";
    players.set(socket.id,p);
    // Socket rooms are connection-scoped. Restore a planetside pilot's room
    // membership when the transient session is rebound, otherwise their world
    // state keeps updating but they stop receiving planet events.
    if(resumed&&p.mode==="planet"&&p.planetId)socket.join(`planet:${p.planetId}`);
    if(p.memberId){
      claimMemberSocket(p.memberId,socket.id);
      const cached=accountLastGoodSnapshots.get(String(p.memberId));
      if(cached&&inventoryPayloadHasItems(cached.invSlots)&&!inventoryPayloadHasItems(p.invSlots))applyPersistedSnapshotPreservingSession(p,cached);
      // Account saves retain progression; this process-local handoff retains
      // the live position when the same signed-in pilot leaves and rejoins
      // before the server resets. Do it after claimMemberSocket so a new tab
      // also inherits the current session's position rather than an old one.
      if(!resumed)restoreAccountLivePosition(p);
    }
    if(!resumed)restorePersistentBuildingsForPlayer(p);
    if(auth&&!resumed)maybeGrantAccountCreationBonus(p,auth,"join");
    applyShipStats(p,false);
    socket.emit("welcome",{id:socket.id,memberId:p.memberId||null,x:p.x,y:p.y,color:p.color,galaxySeed:GALAXY_SEED,prices:economy.snapshot(),playerCount:players.size,shipTypes:SHIP_TYPES,ownedStationTiers:OWNED_STATION_TIERS,structureTypes:PLAYER_STRUCTURE_TYPES,serverName:SERVER_NAME,credits:p.credits,maxSlots:p.maxSlots,invSlots:p.invSlots,level:p.level||1,xp:p.xp||0,xpToNext:playerXpNeeded(p.level||1),attrPoints:p.attrPoints||0,attrs:p.attrs||{},activeMercs:(p.activeMercs||[]).map(publicMerc),equippedWeapon:p.equippedWeapon||"weapon_laser_mk1",weaponLevels:p.weaponLevels||{weapon_laser_mk1:1},equippedAttachments:normalizeAttachments(p.equippedAttachments||{}),planetModules:normalizePlanetModules(p.planetModules||{}),moduleDefs:publicPlanetModuleDefs(),weaponDefs:WEAPON_DEFS,attachmentDefs:ATTACHMENT_DEFS,cosmeticDefs:COSMETIC_DEFS,cosmeticInventory:normalizeCosmeticInventory(p.cosmeticInventory||{}),equippedCosmetics:normalizeEquippedCosmetics(p.equippedCosmetics||{}),stationTierCosmetics:normalizeStationTierCosmetics(p.stationTierCosmetics||{}),planetTypeCosmetics:normalizePlanetTypeCosmetics(p.planetTypeCosmetics||{}),redeemedCoupons:normalizeRedeemedCoupons(p.redeemedCoupons||{}),worldCosmetics:GLOBAL_WORLD_COSMETICS,worldPlanetTypeCosmetics:GLOBAL_PLANET_TYPE_COSMETICS,storyProgress:normalizeStoryProgress(p.storyProgress||{}),resourceDefs:SERVER_RESOURCE_PUBLIC_DEFS,resourceKeys:RES_KEYS,shopResourceKeys:SHOP_RESOURCE_KEYS,resourceCatalogVersion:2,spriteCosmeticRegistryVersion:1,persistenceLoaded:!!p.persistenceLoaded,signupCreditBonusGranted:!!p.signupCreditBonusGranted});
    emitInventorySync(p,"login");sendPlanetModuleState(socket,p);
    socket.broadcast.emit("playerJoined",{id:p.id,name:p.name,color:p.color});
    broadcastChat("Server",`${p.name} has ${resumed?"reconnected to":"entered"} the galaxy.`,"#78ff8a");
    broadcastLeaderboard();broadcastServerList();
    emitOwnedStationsList(socket);
    emitPlayerStructures(socket);
    emitCivilizationZones(socket);
    const mercCat=generateMercOffersForPlayer(p);
    socket.emit("mercOffers",{offers:mercCat.offers,expires:mercCat.expires,activeMercs:(p.activeMercs||[]).map(publicMerc),maxActive:MAX_ACTIVE_MERCS});
  });

  socket.on("respawn",()=>{
    const p=players.get(socket.id);if(!p)return;
    if((Number(p.hp)||0)<=0||p.respawnPending||p.dead)forceRespawnPlayer(p,"manual-request");
  });

  socket.on("linkAccount",async ({token,wixSnapshot})=>{
    const p=players.get(socket.id);if(!p)return;
    const wasAnonymous=!p.memberId;
    let auth=combineAuthWithClientSnapshot(verifyGameToken(token),wixSnapshot);
    auth=await enrichAuthWithPersistedSnapshot(auth,"linkAccount");
    if(!auth){socket.emit("accountLinkDenied",{reason:"Invalid or expired Wix login token."});return;}
    if(p.accountLoaded&&p.memberId&&p.memberId!==String(auth.memberId)){socket.emit("accountLinkDenied",{reason:"This socket is already linked to another account."});return;}
    const linkResult=linkAuthAccountToPlayer(p,auth);
    if(!linkResult.ok){socket.emit("accountLinkDenied",{reason:"Could not link Wix account."});return;}
    if(p.memberId){
      claimMemberSocket(p.memberId,socket.id);
      const cached=accountLastGoodSnapshots.get(String(p.memberId));
      if(cached&&inventoryPayloadHasItems(cached.invSlots)&&!inventoryPayloadHasItems(p.invSlots))applyPersistedSnapshotPreservingSession(p,cached);
      if(wasAnonymous)restoreAccountLivePosition(p);
    }
    if(!linkResult.alreadyLinked)restorePersistentBuildingsForPlayer(p);
    maybeGrantAccountCreationBonus(p,auth,"link_account");
    socket.emit("accountLinked",{memberId:p.memberId,credits:p.credits,maxSlots:p.maxSlots,invSlots:p.invSlots,equippedWeapon:p.equippedWeapon||"weapon_laser_mk1",weaponLevels:p.weaponLevels||{weapon_laser_mk1:1},equippedAttachments:normalizeAttachments(p.equippedAttachments||{}),attachmentDefs:ATTACHMENT_DEFS,planetModules:normalizePlanetModules(p.planetModules||{}),moduleDefs:publicPlanetModuleDefs(),storyProgress:normalizeStoryProgress(p.storyProgress||{}),alreadyLinked:!!linkResult.alreadyLinked,persistenceLoaded:!!p.persistenceLoaded,signupCreditBonusGranted:!!p.signupCreditBonusGranted});
    emitInventorySync(p,linkResult.alreadyLinked?"account_link_confirmed":"account_linked");
    if(!p.persistenceLoaded)socket.emit("accountSyncPending",{reason:"Waiting for Wix inventory snapshot before saving."});
    if(!linkResult.alreadyLinked&&p.persistenceLoaded)persistPlayerSoon(p,"account_linked");
    emitPlayerStructures(socket);
  });



  socket.on("clientLocalSaveSync",({snapshot})=>{
    const p=players.get(socket.id);if(!p||!snapshot||typeof snapshot!=="object")return;
    const credits=Math.max(0,Math.min(100000000,Math.floor(Number(snapshot.credits)||0)));
    if(credits>(p.credits||0))p.credits=credits;
    const slots=normalizeInventorySlots(snapshot.invSlots||[],Math.max(p.maxSlots||24,Math.floor(Number(snapshot.maxSlots)||24)));
    if(inventoryPayloadHasItems(slots)){p.maxSlots=Math.max(p.maxSlots||24,slots.length);p.invSlots=slots;}
    if(snapshot.cosmeticInventory)p.cosmeticInventory={...normalizeCosmeticInventory(snapshot.cosmeticInventory),...normalizeCosmeticInventory(p.cosmeticInventory||{})};
    if(snapshot.equippedCosmetics){
      const snapEq=normalizeEquippedCosmetics(snapshot.equippedCosmetics),curEq=normalizeEquippedCosmetics(p.equippedCosmetics||{}),merged={...snapEq};
      for(const slot of COSMETIC_SLOTS)if(curEq[slot])merged[slot]=curEq[slot];
      p.equippedCosmetics=merged;
      for(const slot of WORLD_COSMETIC_SLOTS)if(merged[slot])applySharedWorldCosmeticSlot(slot,merged[slot]);
    }
    if(snapshot.redeemedCoupons)p.redeemedCoupons={...normalizeRedeemedCoupons(snapshot.redeemedCoupons),...normalizeRedeemedCoupons(p.redeemedCoupons||{})};
    if(snapshot.storyProgress){const incoming=normalizeStoryProgress(snapshot.storyProgress),cur=normalizeStoryProgress(p.storyProgress||{});p.storyProgress=normalizeStoryProgress({completed:Math.max(cur.completed,incoming.completed),startedAt:Math.min(cur.startedAt,incoming.startedAt),updatedAt:Math.max(cur.updatedAt,incoming.updatedAt)});}
    if(snapshot.planetModules&&typeof snapshot.planetModules==="object"){const incoming=normalizePlanetModules(snapshot.planetModules),cur=normalizePlanetModules(p.planetModules||{});for(const k of PLANET_MODULE_ORDER)cur[k]=Math.max(cur[k],incoming[k]);p.planetModules=cur;refreshPlanetSuitStats(p);}
    emitInventorySync(p,"client_local_bootstrap");sendCosmeticState(socket,p,"client_local_bootstrap");persistPlayerSoon(p,"client_local_bootstrap");
  });

  socket.on("input",({rotLeft,rotRight,thrust,brake,shootX,shootY})=>{
    const p=players.get(socket.id);if(!p)return;
    p.input.rotLeft=!!rotLeft;p.input.rotRight=!!rotRight;p.input.thrust=!!thrust;p.input.brake=!!brake;
    if(shootX!==undefined){p.input.shootX=Number(shootX);p.input.shootY=Number(shootY);}
  });

  socket.on("ownedTradeShipAttackPlayer",({targetId,stationKey,shipId,damage,x,y})=>{
    const owner=players.get(socket.id),target=players.get(String(targetId||""));
    if(!owner||!target||owner.mode!=="space"||target.mode!=="space"||target.hp<=0)return;
    if(owner.id===target.id||areAllied(owner,target))return;
    const st=ownedStations.get(String(stationKey||""));
    if(!st||st.ownerId!==owner.id||st.destroyed)return;
    const sh=(st.hiredShips||[]).find(s=>s.id===shipId);
    if(!sh||sh.state==="respawning")return;
    const now=Date.now();
    if(sh.lastAssistShotAt&&now-sh.lastAssistShotAt<560)return;
    const declaredX=Number(x),declaredY=Number(y);
    const stationNearOwner=Math.hypot(owner.x-st.x,owner.y-st.y)<2400;
    const stationNearTarget=Math.hypot(target.x-st.x,target.y-st.y)<2400;
    const declaredShipNearTarget=Number.isFinite(declaredX)&&Number.isFinite(declaredY)&&Math.hypot(target.x-declaredX,target.y-declaredY)<520;
    if(!stationNearOwner&&!stationNearTarget&&!declaredShipNearTarget)return;
    const tierDamage={outpost:7,base:13,fortress:22}[st.tier]||7;
    const safeDamage=Math.max(1,Math.min(tierDamage,Number(damage)||tierDamage));
    sh.lastAssistShotAt=now;
    const result=applySpaceDamageToPlayer(target,safeDamage,owner,"Ally Trade Ship");
    socket.emit("ownedTradeShipAttackConfirm",{targetId:target.id,stationKey:st.key,shipId:sh.id,damage:result.damage});
  });

  socket.on("equipWeapon",({weaponKey})=>{
    const p=players.get(socket.id);weaponKey=String(weaponKey||"");
    if(!p||!isWeaponKey(weaponKey)){socket.emit("weaponDenied",{reason:"Unknown weapon."});return;}
    if(!playerOwnsWeaponForEquip(p,weaponKey)){socket.emit("weaponDenied",{reason:"You do not own that weapon."});return;}
    p.equippedWeapon=weaponKey;p.weaponLevels=p.weaponLevels||{};p.weaponLevels[weaponKey]=weaponLevelFor(p,weaponKey);
    socket.emit("weaponEquipped",{weaponKey,weaponLevels:p.weaponLevels,equippedWeapon:p.equippedWeapon});emitInventorySync(p,"equip_weapon");persistPlayerSoon(p,"equip_weapon");
  });
  socket.on("unequipWeapon",()=>{
    const p=players.get(socket.id);if(!p)return;
    p.equippedWeapon="weapon_laser_mk1";p.weaponLevels=p.weaponLevels||{};p.weaponLevels.weapon_laser_mk1=weaponLevelFor(p,"weapon_laser_mk1");
    socket.emit("weaponEquipped",{weaponKey:p.equippedWeapon,weaponLevels:p.weaponLevels,equippedWeapon:p.equippedWeapon,unequipped:true});emitInventorySync(p,"unequip_weapon");persistPlayerSoon(p,"unequip_weapon");
  });
  socket.on("equipAttachment",(payload={})=>{
    try{
      let attachmentKey=String(payload?.attachmentKey||""),p=players.get(socket.id);
      const def=ATTACHMENT_DEFS[inventoryBaseType(attachmentKey)];
      if(!p||!def){socket.emit("attachmentDenied",{reason:"Unknown attachment."});return;}
      if(inventoryCount(p,attachmentKey)<=0){socket.emit("attachmentDenied",{reason:"You do not own that attachment."});return;}
      p.equippedAttachments=normalizeAttachments(p.equippedAttachments||{});
      p.equippedAttachments[def.slot]=attachmentKey;applyShipStats(p,false);
      socket.emit("attachmentEquipped",{attachmentKey,slot:def.slot,equippedAttachments:normalizeAttachments(p.equippedAttachments||{}),hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield});emitInventorySync(p,"equip_attachment");persistPlayerSoon(p,"equip_attachment");
    }catch(error){console.error("equipAttachment recovered",error);socket.emit("attachmentDenied",{reason:"Module equip could not be completed safely."});}
  });
  socket.on("unequipAttachment",({slot})=>{
    const p=players.get(socket.id);slot=String(slot||"");
    if(!p||!ATTACHMENT_SLOTS.includes(slot)){socket.emit("attachmentDenied",{reason:"Unknown attachment slot."});return;}
    p.equippedAttachments=normalizeAttachments(p.equippedAttachments||{});
    const old=p.equippedAttachments[slot];p.equippedAttachments[slot]=null;applyShipStats(p,false);
    socket.emit("attachmentUnequipped",{attachmentKey:old,slot,equippedAttachments:normalizeAttachments(p.equippedAttachments||{}),hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield});emitInventorySync(p,"unequip_attachment");persistPlayerSoon(p,"unequip_attachment");
  });
  socket.on("upgradeModuleItem",(payload={})=>{
    try{
      const p=players.get(socket.id),key=String(payload?.itemKey||""),m=moduleTierForKey(key);if(!p||!ATTACHMENT_DEFS[m.base]||m.level>=10){socket.emit("moduleUpgradeDenied",{reason:"That module cannot be upgraded further."});return;}
      if(inventoryCount(p,key)<=0){socket.emit("moduleUpgradeDenied",{reason:"Module is no longer in your inventory."});return;}
      const cost=moduleUpgradeCostFor(key);if((p.credits||0)<cost.credits||inventoryCount(p,cost.resource)<cost.amount){socket.emit("moduleUpgradeDenied",{reason:`Need ${cost.credits.toLocaleString()}cr and ${cost.amount} ${cost.resource.replace(/_/g," ")}.`});return;}
      const next=moduleInstanceKey(m.base,m.level+1,m.bonus);if(!canReplaceInventoryItem(p,key,1,next,1)){socket.emit("moduleUpgradeDenied",{reason:"Inventory is full for the upgraded module."});return;}
      p.credits-=cost.credits;removeInventory(p,cost.resource,cost.amount);removeInventory(p,key,1);addInventory(p,next,1);for(const slot of ATTACHMENT_SLOTS)if(p.equippedAttachments?.[slot]===key)p.equippedAttachments[slot]=next;applyShipStats(p,false);
      socket.emit("moduleUpgradeResult",{itemKey:next,base:m.base,level:m.level+1,bonus:m.bonus,cost,credits:p.credits,invSlots:p.invSlots,maxSlots:p.maxSlots,equippedAttachments:normalizeAttachments(p.equippedAttachments||{}),hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield});syncAndPersist(p,"module_upgrade");
    }catch(error){console.error("upgradeModuleItem recovered",error);socket.emit("moduleUpgradeDenied",{reason:"Module upgrade recovered safely. Please try again."});}
  });
  socket.on("convergeModuleItem",(payload={})=>{
    try{
    const p=players.get(socket.id),key=String(payload?.itemKey||""),m=moduleTierForKey(key),use=Math.max(1,Math.min(10,Math.floor(Number(payload?.copies)||1)));if(!p||!ATTACHMENT_DEFS[m.base]){socket.emit("moduleUpgradeDenied",{reason:"Choose a ship module."});return;}
    const pool=MODULE_CONVERGENCE_BONUSES.filter(b=>!m.bonuses.includes(b));
    if(!pool.length){socket.emit("moduleUpgradeDenied",{reason:"This module already has every convergence bonus."});return;}
    if(inventoryCount(p,key)<use){socket.emit("moduleUpgradeDenied",{reason:`Need ${use} matching module${use>1?"s":""}.`});return;}
    const cost=moduleConvergenceCostFor(key,use);if((p.credits||0)<cost.credits||inventoryCount(p,cost.resource)<cost.amount){socket.emit("moduleUpgradeDenied",{reason:`Need ${cost.credits.toLocaleString()}cr and ${cost.amount} ${cost.resource.replace(/_/g," ")}.`});return;}
    // Each selected matching module adds a full ten percentage points; ten
    // copies therefore guarantees the convergence result the UI advertises.
    const chance=Math.min(1,use*.10),roll=Math.random(),addedBonus=pool[Math.floor(Math.random()*pool.length)],nextBonus=[...m.bonuses,addedBonus].sort().join("_");
    const result=moduleInstanceKey(m.base,Math.max(1,m.level),nextBonus);
    if(roll<chance&&!canReplaceInventoryItem(p,key,use,result,1)){socket.emit("moduleUpgradeDenied",{reason:"Inventory full for convergence result."});return;}
    // Convergence is a deliberate gamble: every selected matching module is
    // consumed on either result. The success result carries a unique encoded
    // convergence bonus, so it only stacks with an identical stat line.
    p.credits-=cost.credits;removeInventory(p,cost.resource,cost.amount);removeInventory(p,key,use);let success=roll<chance;
    if(success){
      addInventory(p,result,1);
      for(const slot of ATTACHMENT_SLOTS)if(p.equippedAttachments?.[slot]===key)p.equippedAttachments[slot]=result;
    }else if(inventoryCount(p,key)<=0){
      // A failed convergence still consumes every selected copy.  Never leave
      // a ghost attachment equipped after its final matching module is gone.
      for(const slot of ATTACHMENT_SLOTS)if(p.equippedAttachments?.[slot]===key)p.equippedAttachments[slot]=null;
    }
    applyShipStats(p,false);
    socket.emit("moduleConvergenceResult",{success,chance,result:success?result:key,base:m.base,level:m.level,bonus:success?nextBonus:m.bonus,addedBonus:success?addedBonus:null,copies:use,consumed:use,maxBonuses:MODULE_CONVERGENCE_BONUSES.length,cost,credits:p.credits,invSlots:p.invSlots,maxSlots:p.maxSlots,equippedAttachments:normalizeAttachments(p.equippedAttachments||{}),hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield});syncAndPersist(p,"module_convergence");
    }catch(error){console.error("convergeModuleItem recovered",error);socket.emit("moduleUpgradeDenied",{reason:"Module convergence recovered safely. Please try again."});}
  });
  socket.on("craftAttachmentModule",({moduleKey}={})=>{
    try{
      const p=players.get(socket.id),key=String(moduleKey||""),def=ATTACHMENT_DEFS[key],recipe=MODULE_CRAFT_RECIPES[key];
      if(!p||!def||!recipe){socket.emit("moduleCraftDenied",{reason:"Unknown ship module recipe."});return;}
      const check=canCraftRecipe(p,recipe);
      if(!check.ok){socket.emit("moduleCraftDenied",{reason:check.reason||"Missing module crafting materials."});return;}
      if(!canFitInventory(p,key,1)){socket.emit("moduleCraftDenied",{reason:"Inventory full for this module."});return;}
      consumeCraftRecipe(p,recipe);addInventory(p,key,1);applyShipStats(p,false);
      socket.emit("moduleCraftResult",{moduleKey:key,credits:p.credits,invSlots:p.invSlots,maxSlots:p.maxSlots,equippedAttachments:normalizeAttachments(p.equippedAttachments||{}),hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield});
      syncAndPersist(p,"craft_attachment_module");
    }catch(error){console.error("craftAttachmentModule recovered",error);socket.emit("moduleCraftDenied",{reason:"Module craft recovered safely. Please try again."});}
  });
  socket.on("upgradeWeapon",({weaponKey})=>{
    const p=players.get(socket.id);weaponKey=String(weaponKey||"");
    if(!p||!isWeaponKey(weaponKey)){socket.emit("weaponDenied",{reason:"Unknown weapon."});return;}
    if(inventoryCount(p,weaponKey)<=0){socket.emit("weaponDenied",{reason:"You do not own that weapon."});return;}
    p.weaponLevels=p.weaponLevels||{};const cost=weaponUpgradeCost(p,weaponKey);
    if((p.credits||0)<cost){socket.emit("weaponDenied",{reason:`Need ${cost}cr to upgrade this weapon.`});return;}
    p.credits-=cost;p.weaponLevels[weaponKey]=weaponLevelFor(p,weaponKey)+1;
    socket.emit("weaponUpgraded",{weaponKey,level:p.weaponLevels[weaponKey],credits:p.credits,weaponLevels:p.weaponLevels});syncAndPersist(p,"upgrade_weapon");
  });
  socket.on("craftWeapon",({weaponKey})=>{
    const p=players.get(socket.id);weaponKey=String(weaponKey||"");
    const def=WEAPON_DEFS[weaponKey];
    if(!p||!def||!def.recipe){socket.emit("craftWeaponDenied",{reason:"Unknown craftable weapon."});return;}
    const check=canCraftRecipe(p,def.recipe);
    if(!check.ok){socket.emit("craftWeaponDenied",{reason:check.reason||"Missing parts."});return;}
    if(!canFitInventory(p,weaponKey,1)){socket.emit("craftWeaponDenied",{reason:"Inventory full."});return;}
    consumeCraftRecipe(p,def.recipe); addInventory(p,weaponKey,1); p.weaponLevels=p.weaponLevels||{}; if(!p.weaponLevels[weaponKey])p.weaponLevels[weaponKey]=1;
    socket.emit("craftWeaponConfirm",{weaponKey,credits:p.credits,invSlots:p.invSlots,maxSlots:p.maxSlots,weaponLevels:p.weaponLevels});
    syncAndPersist(p,"craft_weapon");
  });
  socket.on("setCivilizationStationTask",({zoneId,stationId,task,targetZoneId,targetZone})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="space")return;
    zoneId=safeZoneId(zoneId);stationId=safeZoneId(stationId);task=task==="attack"?"attack":task==="idle"?"idle":"mine";targetZoneId=safeZoneId(targetZoneId);
    const zone=civilizationZones.get(zoneId);if(!zone||!playerOwnsCivilizationZone(p,zone)){socket.emit("civilizationTaskDenied",{reason:"You do not own that civilization zone."});return;}
    if(Math.hypot(p.x-zone.x,p.y-zone.y)>660){socket.emit("civilizationTaskDenied",{reason:"Command ships from the main super station."});return;}
    ensureCivLogistics(zone);const selectedStation=civStation(zone,stationId);
    if(!stationId||!selectedStation){socket.emit("civilizationTaskDenied",{reason:"Select one of this civilization's stations."});return;}
    let targetInfo=null;
    if(task==="attack"){
      if(!targetZoneId||targetZoneId===zoneId){socket.emit("civilizationTaskDenied",{reason:"Choose a different civilization zone to attack."});return;}
      const ownedTarget=civilizationZones.get(targetZoneId);
      if(ownedTarget){
        targetInfo={zoneId:ownedTarget.zoneId,name:ownedTarget.name,x:ownedTarget.x,y:ownedTarget.y,radius:ownedTarget.radius,baseStationCount:ownedTarget.baseStationCount,color:ownedTarget.color};
      }else{
        const generatedTarget=safeCivZoneInput(targetZone||{});
        if(!generatedTarget||generatedTarget.zoneId!==targetZoneId){socket.emit("civilizationTaskDenied",{reason:"Target zone data was missing. Reopen the super station menu and choose a target zone again."});return;}
        targetInfo=generatedTarget;
      }
      const targetDist=Math.hypot((targetInfo.x||0)-zone.x,(targetInfo.y||0)-zone.y);
      if(!Number.isFinite(targetDist)||targetDist>8000){socket.emit("civilizationTaskDenied",{reason:"That civilization zone is too far from this command station."});return;}
    }
    zone.ownerId=p.id;zone.ownerName=p.name;zone.stationTasks=zone.stationTasks||{};zone.stationTasks[stationId]={
      task,
      targetZoneId:task==="attack"?targetZoneId:null,
      targetName:task==="attack"?(targetInfo?.name||""):"",
      targetX:task==="attack"?Math.round(Number(targetInfo?.x)||0):0,
      targetY:task==="attack"?Math.round(Number(targetInfo?.y)||0):0,
      targetRadius:task==="attack"?Math.round(Number(targetInfo?.radius)||0):0,
      targetColor:task==="attack"?(targetInfo?.color||""):"",
      updatedAt:Date.now(),
      war:false
    };
    if(task==="attack"&&targetZoneId){
      ensureCivLogistics(zone);zone.relations[targetZoneId]="enemy";
      // A persistent player-owned target receives a reciprocal war order.
      // Procedural NPC zones retaliate on the client as soon as the first raid
      // lands; this branch keeps the same rule across connected players.
      const defendingZone=civilizationZones.get(targetZoneId);
      if(defendingZone&&!playerOwnsCivilizationZone(p,defendingZone)){
        ensureCivLogistics(defendingZone);defendingZone.relations[zoneId]="enemy";defendingZone.stationTasks=defendingZone.stationTasks||{};
        for(const defender of civAllStations(defendingZone)){
          defendingZone.stationTasks[defender.id]=civAttackTask(zone,true);
        }
      }
    }
    socket.emit("civilizationStationTaskSet",{zone:publicCivilizationZone(zone,p.id),stationId,task,targetZoneId});broadcastCivilizationZonesList();persistPlayerSoon(p,"civilization_station_task");
  });
  socket.on("setAllCivilizationStationTasks",({zoneId,task,targetZoneId,targetZone})=>{
    const p=players.get(socket.id);zoneId=safeZoneId(zoneId);task=task==="attack"?"attack":task==="idle"?"idle":"mine";targetZoneId=safeZoneId(targetZoneId);
    const zone=civilizationZones.get(zoneId);if(!p||!zone||!playerOwnsCivilizationZone(p,zone)){socket.emit("civilizationTaskDenied",{reason:"You do not own that civilization zone."});return;}
    if(Math.hypot(p.x-zone.x,p.y-zone.y)>660){socket.emit("civilizationTaskDenied",{reason:"Command fleets from the super station."});return;}
    let target=null;if(task==="attack"){target=civilizationZones.get(targetZoneId)||targetZone;if(!targetZoneId||targetZoneId===zoneId||!target){socket.emit("civilizationTaskDenied",{reason:"Choose a nearby civilization target."});return;}}
    ensureCivLogistics(zone);zone.stationTasks=zone.stationTasks||{};
    for(const st of civAllStations(zone))zone.stationTasks[st.id]=task==="attack"?civAttackTask(target,false):task==="idle"?civIdleTask():civMineTask();
    if(task==="attack"){zone.relations[targetZoneId]="enemy";const defender=civilizationZones.get(targetZoneId);if(defender&&!playerOwnsCivilizationZone(p,defender)){ensureCivLogistics(defender);defender.relations[zoneId]="enemy";defender.stationTasks=defender.stationTasks||{};for(const st of civAllStations(defender))defender.stationTasks[st.id]=civAttackTask(zone,true);}}
    socket.emit("civilizationAllTasksSet",{zone:publicCivilizationZone(zone,p.id),task,targetZoneId});broadcastCivilizationZonesList();persistPlayerSoon(p,"civilization_all_station_tasks");
  });
  socket.on("recallCivilizationShips",({zoneId})=>{
    const {p,zone}=ownCivZone({zoneId});if(!p||!zone)return;
    const now=Date.now();zone.stationTasks=zone.stationTasks||{};
    for(const st of civAllStations(zone)){
      zone.stationTasks[st.id]=civIdleTask(now);st.lastTaskHeartbeat=now;
      const fleetById=new Map(civStationMiningFleet(st).map(craft=>[craft.id,craft]));
      // Loaded holds are the only exception to the immediate idle order: they
      // make one last return leg and deposit at their own station, then join
      // the station's even defense formation.
      for(const [shipId,cargo] of Object.entries(st.miningCargo||{}))if(Number(cargo?.amount)>0)civReturnCargo(cargo,st,fleetById.get(shipId)||{speed:civDefaultShipSpeed(st.tier)},now);
      for(const sh of st.shipRoster||[])if(sh.status!=="destroyed")sh.assignedTask="idle";
    }
    socket.emit("civilizationShipsRecalled",{zoneId:zone.zoneId,zone:publicCivilizationZone(zone,p.id)});
    civSync(p,zone,"civilization_ship_recall");
  });
  socket.on("refreshCivilizationShips",({zoneId})=>{const {p,zone}=ownCivZone({zoneId});if(!p||!zone)return;ensureCivLogistics(zone);for(const st of civAllStations(zone)){st.lastTaskHeartbeat=Date.now();for(const sh of st.shipRoster||[])if(sh.status!=="destroyed")sh.status="active";}socket.emit("civilizationShipsRefreshed",{zoneId:zone.zoneId,zone:publicCivilizationZone(zone,p.id)});civSync(p,zone,"civilization_ship_refresh");});

  socket.on("modeChange",({mode,planetId,x,y})=>{
    const p=players.get(socket.id);if(!p)return;
    if(p.planetId)socket.leave(`planet:${p.planetId}`);
    p.mode=mode;p.planetId=planetId||null;p.activePlanetMine=null;if(p.planetId)socket.join(`planet:${p.planetId}`);if(x!==undefined){p.x=x;p.y=y;}refreshPlanetSuitStats(p);sendPlanetModuleState(socket,p);
    if(mode==="space"){p.planetX=0;p.planetY=0;p.planetVx=0;p.planetVy=0;p.planetTool="mining";}
  });



  socket.on("requestPlanetMap",({planet,requestId}={})=>{
    const p=players.get(socket.id);if(!p)return;
    let safePlanet=null;
    try{
      safePlanet=safePlanetInfo(planet);
      if(!safePlanet.id)throw new Error("Missing planet identifier.");
      const map=getPlanetMap(safePlanet);
      if(!map||!map.planet||!map.W||!map.H||!map.tiles)throw new Error("Planet map generation returned incomplete data.");
      if(p.planetId)socket.leave(`planet:${p.planetId}`);
      p.mode="planet";p.planetId=map.planet.id;p.currentPlanetInfo=map.planet;p.activePlanetMine=null;refreshPlanetSuitStats(p);socket.join(`planet:${map.planet.id}`);sendPlanetModuleState(socket,p);
      socket.emit("planetMapState",{requestId:requestId||null,planetId:map.planet.id,W:map.W,H:map.H,tiles:Array.from(map.tiles),hp:Array.from(map.hp),heights:map.heights});
    }catch(error){
      console.error("Planet map request failed",{socketId:socket.id,planetId:safePlanet?.id||planet?.id,error});
      socket.emit("planetMapError",{requestId:requestId||null,planetId:safePlanet?.id||String(planet?.id||""),reason:"Planet map generation failed. The client will retry automatically."});
    }
  });

  socket.on("minePlanetTile",(payload={},ack)=>{
    let {phase,planetId,tx,ty,power,oneClick,requestId,clientX,clientY}=payload||{};
    const p=players.get(socket.id),requestKey=String(requestId||"");
    const mineReply=payload2=>{if(typeof ack==="function")try{ack({requestId:requestKey,...payload2});}catch(_){}};
    if(!p){mineReply({ok:false,reason:"Player session unavailable."});return;}
    const now=Date.now();if(!(p._recentPlanetMineResults instanceof Map))p._recentPlanetMineResults=new Map();for(const [id,result] of p._recentPlanetMineResults)if(now-(result?.completedAt||0)>15000)p._recentPlanetMineResults.delete(id);
    planetId=String(planetId||"");phase=String(phase||"");
    if(phase==="cancel"){if(p.activePlanetMine?.requestId===requestKey)p.activePlanetMine=null;mineReply({ok:true,cancelled:true});return;}
    const cached=requestKey?p._recentPlanetMineResults.get(requestKey):null;if(cached&&phase==="complete"){mineReply({...cached,duplicate:true});return;}
    let map=planetMaps.get(planetId);if(!map&&p.currentPlanetInfo?.id===planetId)map=getPlanetMap(p.currentPlanetInfo);
    const deny=(reason,x,y)=>{socket.emit("planetMineDenied",{planetId,requestId:requestKey,reason,x,y});mineReply({ok:false,reason});};
    if(!map){deny("Planet map was not ready. Reloading the planet map.");return;}
    if(p.mode!=="planet"||p.planetId!==planetId){if(p.planetId)socket.leave(`planet:${p.planetId}`);p.mode="planet";p.planetId=planetId;refreshPlanetSuitStats(p);socket.join(`planet:${planetId}`);sendPlanetModuleState(socket,p);}
    tx=Math.floor(Number(tx));ty=Math.floor(Number(ty));
    if(!Number.isFinite(tx)||!Number.isFinite(ty)||tx<0||ty<0||tx>=map.W||ty>=map.H-3){deny("Mining target is outside this planet.");return;}
    if(Number.isFinite(Number(clientX))&&Number.isFinite(Number(clientY))){p.planetX=Number(clientX);p.planetY=Number(clientY);}
    const id=ty*map.W+tx,t=map.tiles[id],dropX=tx*16+8,dropY=ty*16+8,px=Number.isFinite(Number(clientX))?Number(clientX):Number(p.planetX)||0,py=Number.isFinite(Number(clientY))?Number(clientY):Number(p.planetY)||0;
    if(Math.hypot(dropX-px,dropY-py)>185){deny("That tile is out of mining range.",dropX,dropY);return;}
    if(!t){deny("Empty tile — continuing to the next block.",dropX,dropY);return;}
    if(ty>=map.H-3){deny("Bedrock cannot be mined.",dropX,dropY);return;}
    let kind=planetResForTile(map.planet,t,tx,ty,map.H);if(!RES_KEYS.includes(kind))kind="stone";
    const oldHp=Math.max(1,Math.floor(Number(map.hp[id])||1)),rarity=Math.max(1,Number(RES_RARITY[kind])||1),level=Math.max(1,Number(p.miningLevel)||1);
    const moduleFx=planetModuleEffects(p),requiredMs=Math.max(420,Math.min(2400,Math.round(((700+rarity*140+Math.min(650,oldHp*4))/(1+(level-1)*.08))*moduleFx.miningSpeedMult)));

    if(phase==="start"){
      const current=p.activePlanetMine;
      if(current&&current.requestId===requestKey&&current.planetId===planetId&&current.tx===tx&&current.ty===ty){mineReply({ok:true,phase:"start",requiredMs:current.requiredMs,kind:current.kind,tx,ty,resumed:true});return;}
      p.activePlanetMine={requestId:requestKey,planetId,tx,ty,tile:t,kind,startedAt:Date.now(),requiredMs};
      mineReply({ok:true,phase:"start",requiredMs,kind,tx,ty});return;
    }

    if(phase==="complete"){
      const session=p.activePlanetMine;
      if(!session||session.requestId!==requestKey||session.planetId!==planetId||session.tx!==tx||session.ty!==ty){deny("Mining hold expired — continuing from the current tile.",dropX,dropY);return;}
      const elapsed=Date.now()-session.startedAt,remainingMs=Math.max(0,session.requiredMs-elapsed);
      if(remainingMs>90){mineReply({ok:false,waiting:true,remainingMs,requiredMs:session.requiredMs,kind:session.kind,tx,ty});return;}
      if(map.tiles[id]!==session.tile){p.activePlanetMine=null;deny("That tile changed before mining completed.",dropX,dropY);return;}
      const qty=(t===3||t===4)?(Math.random()<0.35?2:1):(t===5?(Math.random()<0.55?2:1):1);
      if(!canFitInventory(p,kind,qty)){p.activePlanetMine=null;deny("Inventory full — empty a slot before mining more.",dropX,dropY);return;}
      map.tiles[id]=0;map.hp[id]=0;p.activePlanetMine=null;
      if(!addInventory(p,kind,qty)){map.tiles[id]=t;map.hp[id]=oldHp;deny("Inventory changed while mining — tile restored.",dropX,dropY);return;}
      const result={ok:true,phase:"complete",planetId,kind,qty,tx,ty,x:dropX,y:dropY,credits:p.credits||0,maxSlots:p.maxSlots||24,invSlots:(p.invSlots||emptySlots(24)).map(s=>s?{type:s.type||null,count:Number(s.count)||0}:{type:null,count:0}),completedAt:Date.now()};
      if(requestKey)p._recentPlanetMineResults.set(requestKey,result);
      mineReply(result);
      io.to(`planet:${planetId}`).emit("planetTileUpdate",{planetId,requestId:requestKey,tx,ty,tile:0,hp:0});
      io.to(`planet:${planetId}`).emit("planetMineDrop",{planetId,requestId:requestKey,kind,x:dropX,y:dropY,qty,ownerId:p.id});
      socket.emit("planetMineReward",result);
      syncAndPersist(p,"planet_mine");grantXp(p,rarity*2,"Mining");return;
    }

    // Legacy support for older mobile/browser clients that still send one-click or damage-tick requests.
    const dmg=oneClick?oldHp:Math.max(1,Math.min(80,Number(power)||18)),nextHp=Math.max(0,oldHp-dmg);
    if(nextHp<=0){
      const qty=(t===3||t===4)?(Math.random()<0.35?2:1):(t===5?(Math.random()<0.55?2:1):1);
      if(!canFitInventory(p,kind,qty)){deny("Inventory full — empty a slot before mining more.",dropX,dropY);return;}
      map.tiles[id]=0;map.hp[id]=0;
      if(!addInventory(p,kind,qty)){map.tiles[id]=t;map.hp[id]=oldHp;deny("Inventory changed while mining — tile restored.",dropX,dropY);return;}
      io.to(`planet:${planetId}`).emit("planetTileUpdate",{planetId,requestId:requestKey,tx,ty,tile:0,hp:0});io.to(`planet:${planetId}`).emit("planetMineDrop",{planetId,requestId:requestKey,kind,x:dropX,y:dropY,qty,ownerId:p.id});socket.emit("planetMineReward",{planetId,requestId:requestKey,kind,x:dropX,y:dropY,qty,credits:p.credits||0,maxSlots:p.maxSlots||24,invSlots:p.invSlots||emptySlots(24)});mineReply({ok:true,planetId,kind,qty,tx,ty,x:dropX,y:dropY});syncAndPersist(p,"planet_mine");grantXp(p,rarity*2,"Mining");
    }else{map.hp[id]=nextHp;io.to(`planet:${planetId}`).emit("planetTileUpdate",{planetId,requestId:requestKey,tx,ty,tile:t,hp:map.hp[id]});mineReply({ok:true,partial:true,hp:map.hp[id],tx,ty});}
  });

  socket.on("placePlanetTile",({planetId,tx,ty,tile,resourceType})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="planet"||p.planetId!==planetId)return;
    const map=planetMaps.get(planetId);if(!map)return;
    tx=Math.floor(Number(tx));ty=Math.floor(Number(ty));tile=Math.floor(Number(tile));
    const valid=[1,2,6,8,10,11,13];
    if(!valid.includes(tile)){socket.emit("planetBuildDenied",{reason:"Invalid build tile.",resourceType});return;}
    if(tx<1||ty<1||tx>=map.W-1||ty>=map.H-3){socket.emit("planetBuildDenied",{reason:"Cannot build there.",resourceType});return;}
    const id=ty*map.W+tx;if(map.tiles[id]){socket.emit("planetBuildDenied",{reason:"Tile occupied.",resourceType});return;}
    resourceType=String(resourceType||"");
    if(BUILD_RESOURCE_TO_TILE[resourceType]!==tile){socket.emit("planetBuildDenied",{reason:"Build material does not match tile.",resourceType});return;}
    if(!removeInventory(p,resourceType,1)){socket.emit("planetBuildDenied",{reason:"No build material in server inventory.",resourceType});return;}
    map.tiles[id]=tile;map.hp[id]=hpForPlacedTile(tile);
    io.to(`planet:${planetId}`).emit("planetTileUpdate",{planetId,tx,ty,tile,hp:map.hp[id]});
    syncAndPersist(p,"planet_build");
  });

  socket.on("planetState",({planetId,x,y,vx,vy,onGround,tool,cosmeticColor,suitColor})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="planet"||p.planetId!==planetId)return;
    p.planetX=Math.max(0,Math.min(99999,Number(x)||0));
    p.planetY=Math.max(0,Math.min(99999,Number(y)||0));
    p.planetVx=Number(vx)||0;p.planetVy=Number(vy)||0;p.planetTool=tool==="weapon"?"weapon":"mining";
    if(cosmeticColor)p.cosmeticColor=String(cosmeticColor).slice(0,24);
    if(suitColor)p.suitColor=String(suitColor).slice(0,24);
  });

  socket.on("planetAttack",({targetId,planetId})=>{
    const p=players.get(socket.id),t=players.get(targetId);
    if(!p||!t||p.mode!=="planet"||t.mode!=="planet"||p.planetId!==planetId||t.planetId!==planetId){socket.emit("planetAttackDenied",{reason:"Target unavailable."});return;}
    if(areAllied(p,t)){socket.emit("planetAttackDenied",{reason:"Friendly fire disabled."});return;}
    const d=Math.hypot((p.planetX||0)-(t.planetX||0),(p.planetY||0)-(t.planetY||0));
    if(d>85){socket.emit("planetAttackDenied",{reason:"Target out of range."});return;}
    const raw=planetWeaponDamage(p), armor=1+((t.attrs.armor-1)*0.08), dmg=planetDamageAfterModules(t,raw/armor);
    t.hp=Math.max(0,t.hp-dmg);t.lastPlanetAttacker=p.id;
    socket.emit("planetAttackConfirm",{targetId:t.id,damage:Math.round(dmg),hp:t.hp});
    io.to(t.id).emit("planetHit",{damage:Math.round(dmg),hp:t.hp,attackerName:p.name});
    if(t.hp<=0){
      t.deaths=(t.deaths||0)+1;p.kills=(p.kills||0)+1;p.credits+=75;addScore(p,250,"Planet PvP");
      io.to(p.id).emit("creditUpdate",{credits:p.credits});
      io.to(t.id).emit("youDied",{killedBy:p.name});
      io.emit("playerKilled",{victimId:t.id,victimName:t.name,killerId:p.id,killerName:p.name});
      setTimeout(()=>{const rp=players.get(t.id);if(!rp)return;if(rp.planetId)io.sockets.sockets.get(t.id)?.leave(`planet:${rp.planetId}`);const sp=computeSpawnPoint();rp.mode="space";rp.planetId=null;refreshPlanetSuitStats(rp);rp.x=sp.x;rp.y=sp.y;rp.hp=rp.maxHp;rp.shield=rp.maxShield;rp.energy=100;rp.planetX=0;rp.planetY=0;io.to(t.id).emit("respawn",{x:rp.x,y:rp.y});},3000);
      broadcastLeaderboard();
    }
  });

  socket.on("planetFireProjectile",({planetId,x,y,targetX,targetY})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="planet"||p.planetId!==planetId||p.hp<=0)return;
    const now=Date.now();if((p.planetShootAt||0)>now){socket.emit("planetAttackDenied",{reason:"Weapon cooling down."});return;}
    x=Number(x);y=Number(y);targetX=Number(targetX);targetY=Number(targetY);
    if(!Number.isFinite(x)||!Number.isFinite(y)||!Number.isFinite(targetX)||!Number.isFinite(targetY))return;
    if(Math.hypot(x-(p.planetX||0),y-((p.planetY||0)-8))>50)return;
    const ang=Math.atan2(targetY-y,targetX-x);
    const planetCooldown=Math.max(95,Math.round(180*planetModuleEffects(p).weaponCooldownMult));p.planetShootAt=now+planetCooldown;
    planetProjectiles.push({id:`pp_${p.id}_${now}_${Math.floor(Math.random()*9999)}`,planetId,ownerId:p.id,ownerName:p.name,x,y,vx:Math.cos(ang)*PLANET_PROJ_SPEED,vy:Math.sin(ang)*PLANET_PROJ_SPEED,damage:planetWeaponDamage(p),life:PLANET_PROJ_LIFE});
    socket.emit("planetShotAccepted",{planetId,x,y,targetX,targetY,cooldownMs:planetCooldown});
  });

  socket.on("craftPlanetModule",({moduleKey,requestId}={})=>{
    const p=players.get(socket.id);moduleKey=String(moduleKey||"");const def=PLANET_MODULE_DEFS[moduleKey];
    if(!p||!def){socket.emit("planetModuleDenied",{requestId,reason:"Unknown planetside module."});return;}
    if(p.mode!=="planet"){socket.emit("planetModuleDenied",{requestId,reason:"Land on a planet before using the Module Forge."});return;}
    const now=Date.now();if((p._planetModuleCraftAt||0)>now-250){socket.emit("planetModuleDenied",{requestId,reason:"Module forge is still cooling down."});return;}p._planetModuleCraftAt=now;
    p.planetModules=normalizePlanetModules(p.planetModules||{});const current=p.planetModules[moduleKey]||0;if(current>=PLANET_MODULE_MAX_LEVEL){socket.emit("planetModuleDenied",{requestId,reason:"That module is already maximum level."});return;}
    const recipe=planetModuleRecipe(moduleKey,current),check=canCraftRecipe(p,recipe);if(!check.ok){socket.emit("planetModuleDenied",{requestId,reason:check.reason.replace(/([a-z0-9_]+)/i,m=>SERVER_RESOURCE_PUBLIC_DEFS[m]?.name||m)});return;}
    consumeCraftRecipe(p,recipe);p.planetModules[moduleKey]=current+1;refreshPlanetSuitStats(p);
    socket.emit("planetModuleCrafted",{requestId,moduleKey,level:p.planetModules[moduleKey],planetModules:normalizePlanetModules(p.planetModules),credits:p.credits,invSlots:p.invSlots,maxSlots:p.maxSlots,hp:p.hp,maxHp:p.maxHp,recipe});
    sendPlanetModuleState(socket,p);syncAndPersist(p,"craft_planet_module");
  });

  socket.on("buyCosmetic",({key})=>{
    const p=players.get(socket.id);if(!p)return;
    key=String(key||"");const def=COSMETIC_DEFS[key];
    if(!def){socket.emit("cosmeticDenied",{reason:"Unknown cosmetic."});return;}
    p.cosmeticInventory=normalizeCosmeticInventory(p.cosmeticInventory||{});
    p.equippedCosmetics=normalizeEquippedCosmetics(p.equippedCosmetics||{});
    if(p.cosmeticInventory[key]){socket.emit("cosmeticDenied",{reason:"You already own that cosmetic."});sendCosmeticState(socket,p,"already_owned");return;}
    const cost=Math.max(0,Math.floor(Number(def.price)||0));
    if((p.credits||0)<cost){socket.emit("cosmeticDenied",{reason:`Need ${cost.toLocaleString()} credits.`});return;}
    p.credits=(p.credits||0)-cost;p.cosmeticInventory[key]=true;p.planetTypeCosmetics=normalizePlanetTypeCosmetics(p.planetTypeCosmetics||{});
    if(def.slot==="planet"){const type=planetTypeForCosmetic(def);p.planetTypeCosmetics[type]=key;GLOBAL_PLANET_TYPE_COSMETICS[type]=key;}else{p.equippedCosmetics[def.slot]=key;applySharedWorldCosmeticSlot(def.slot,key);}const zonesChanged=syncOwnedZoneCosmeticsForPlayer(p);
    socket.emit("creditUpdate",{credits:p.credits});sendCosmeticState(socket,p,"bought");socket.broadcast.emit("cosmeticPeerUpdate",{id:p.id,equippedCosmetics:normalizeEquippedCosmetics(p.equippedCosmetics||{})});io.emit("worldCosmeticSync",{worldCosmetics:GLOBAL_WORLD_COSMETICS,planetTypeCosmetics:GLOBAL_PLANET_TYPE_COSMETICS});if(zonesChanged){broadcastCivilizationZonesList();broadcastPlayerStructuresList();}persistPlayerSoon(p,"cosmetic_bought");
  });

  socket.on("equipCosmetic",({key,slot})=>{
    const p=players.get(socket.id);if(!p)return;
    key=String(key||"");slot=String(slot||COSMETIC_DEFS[key]?.slot||"");
    p.cosmeticInventory=normalizeCosmeticInventory(p.cosmeticInventory||{});
    p.equippedCosmetics=normalizeEquippedCosmetics(p.equippedCosmetics||{});
    if(key){
      const def=COSMETIC_DEFS[key];
      if(!def||def.slot!==slot){socket.emit("cosmeticDenied",{reason:"That cosmetic does not fit this slot."});return;}
      if(!p.cosmeticInventory[key]){socket.emit("cosmeticDenied",{reason:"Buy that cosmetic first."});return;}
      if(slot==="planet"){p.planetTypeCosmetics=normalizePlanetTypeCosmetics(p.planetTypeCosmetics||{});const type=planetTypeForCosmetic(def);p.planetTypeCosmetics[type]=key;GLOBAL_PLANET_TYPE_COSMETICS[type]=key;}else{p.equippedCosmetics[slot]=key;applySharedWorldCosmeticSlot(slot,key);}
    }
    else if(COSMETIC_SLOTS.includes(slot)){
      if(slot==="planet"){p.planetTypeCosmetics=normalizePlanetTypeCosmetics({});GLOBAL_PLANET_TYPE_COSMETICS=normalizePlanetTypeCosmetics({});}else{p.equippedCosmetics[slot]=null;applySharedWorldCosmeticSlot(slot,null);}
    }
    else {socket.emit("cosmeticDenied",{reason:"Unknown cosmetic slot."});return;}
    const zonesChanged=syncOwnedZoneCosmeticsForPlayer(p);
    sendCosmeticState(socket,p,"equipped");
    socket.broadcast.emit("cosmeticPeerUpdate",{id:p.id,equippedCosmetics:normalizeEquippedCosmetics(p.equippedCosmetics||{})});
    io.emit("worldCosmeticSync",{worldCosmetics:GLOBAL_WORLD_COSMETICS,planetTypeCosmetics:GLOBAL_PLANET_TYPE_COSMETICS});
    if(zonesChanged){broadcastCivilizationZonesList();broadcastPlayerStructuresList();}
    persistPlayerSoon(p,"cosmetic_equipped");
  });


  socket.on("assignPlanetTypeCosmetic",({type,key})=>{
    const p=players.get(socket.id);if(!p)return;type=String(type||"");key=String(key||"");
    if(!PLANET_VISUAL_TYPES.includes(type)){socket.emit("cosmeticDenied",{reason:"Unknown planet resource type."});return;}
    p.planetTypeCosmetics=normalizePlanetTypeCosmetics(p.planetTypeCosmetics||{});
    if(key){const def=COSMETIC_DEFS[key];if(!def||def.slot!=="planet"){socket.emit("cosmeticDenied",{reason:"That cosmetic is not a planet design."});return;}if(!p.cosmeticInventory?.[key]){socket.emit("cosmeticDenied",{reason:"Buy that planet cosmetic first."});return;}const allowed=Array.isArray(def.planetTypes)&&def.planetTypes.length?def.planetTypes:[type];if(!allowed.includes(type)){socket.emit("cosmeticDenied",{reason:"That planet design is mapped to a different resource-world type."});return;}p.planetTypeCosmetics[type]=key;GLOBAL_PLANET_TYPE_COSMETICS[type]=key;}else{p.planetTypeCosmetics[type]=null;GLOBAL_PLANET_TYPE_COSMETICS[type]=null;}
    socket.emit("planetTypeCosmeticsUpdated",{planetTypeCosmetics:normalizePlanetTypeCosmetics(p.planetTypeCosmetics),worldPlanetTypeCosmetics:GLOBAL_PLANET_TYPE_COSMETICS});sendCosmeticState(socket,p,"planet_type_assigned");io.emit("worldCosmeticSync",{worldCosmetics:GLOBAL_WORLD_COSMETICS,planetTypeCosmetics:GLOBAL_PLANET_TYPE_COSMETICS});persistPlayerSoon(p,"planet_type_cosmetic");
  });

  socket.on("assignStationTierCosmetic",({tier,key})=>{
    const p=players.get(socket.id);if(!p)return;tier=String(tier||"");key=String(key||"");
    if(!STATION_VISUAL_TIERS.includes(tier)){socket.emit("cosmeticDenied",{reason:"Unknown station tier."});return;}
    p.stationTierCosmetics=normalizeStationTierCosmetics(p.stationTierCosmetics||{});
    if(key){const def=COSMETIC_DEFS[key];if(!def||def.slot!=="station"){socket.emit("cosmeticDenied",{reason:"That cosmetic is not a station design."});return;}if(!p.cosmeticInventory?.[key]){socket.emit("cosmeticDenied",{reason:"Buy that station cosmetic first."});return;}p.stationTierCosmetics[tier]=key;}else p.stationTierCosmetics[tier]=null;
    const zonesChanged=syncOwnedZoneCosmeticsForPlayer(p);socket.emit("stationTierCosmeticsUpdated",{stationTierCosmetics:normalizeStationTierCosmetics(p.stationTierCosmetics)});sendCosmeticState(socket,p,"station_tier_assigned");if(zonesChanged)broadcastCivilizationZonesList();persistPlayerSoon(p,"station_tier_cosmetic");
  });

  socket.on("redeemCoupon",({code})=>{
    const p=players.get(socket.id);if(!p)return;
    code=String(code||"").trim().toUpperCase().replace(/[^A-Z0-9_-]/g,"").slice(0,40);
    const def=COUPON_DEFS[code];
    if(!def){socket.emit("couponDenied",{reason:"Coupon code not found."});return;}
    p.redeemedCoupons=normalizeRedeemedCoupons(p.redeemedCoupons||{});
    if(!def.reusable&&p.redeemedCoupons[code]){socket.emit("couponDenied",{reason:"Coupon already redeemed on this pilot."});return;}
    const credits=Math.max(0,Math.floor(Number(def.credits)||0));
    if(!def.reusable)p.redeemedCoupons[code]=true;
    p.credits=(p.credits||0)+credits;
    socket.emit("couponConfirm",{code,creditsAdded:credits,credits:p.credits,description:def.description||"Coupon",reusable:!!def.reusable});
    socket.emit("creditUpdate",{credits:p.credits});sendCosmeticState(socket,p,"coupon");persistPlayerSoon(p,"coupon_redeemed");
  });

  socket.on("characterCosmetic",({cosmeticColor,suitColor})=>{
    const p=players.get(socket.id);if(!p)return;
    if(cosmeticColor)p.cosmeticColor=String(cosmeticColor).slice(0,24);
    if(suitColor)p.suitColor=String(suitColor).slice(0,24);
    sendCharacterState(socket,p);
  });

  socket.on("upgradeCharacterPart",({kind})=>{
    const p=players.get(socket.id);if(!p)return;
    if(!["weapon","mining","oxygen"].includes(kind)){socket.emit("characterUpgradeDenied",{reason:"Unknown upgrade."});return;}
    const cost=characterUpgradeCost(p,kind);if(p.credits<cost){socket.emit("characterUpgradeDenied",{reason:`Need ${cost}cr.`});return;}
    const key={weapon:"weaponLevel",mining:"miningLevel",oxygen:"oxygenLevel"}[kind];
    if((p[key]||1)>=10){socket.emit("characterUpgradeDenied",{reason:"Already maxed."});return;}
    p.credits-=cost;p[key]=(p[key]||1)+1;
    socket.emit("characterUpgradeConfirm",{kind,level:p[key],credits:p.credits});
  });

  socket.on("tradeRequest",({targetId})=>{
    const p=players.get(socket.id),t=players.get(targetId);
    if(!p||!t||p.id===t.id){socket.emit("tradeDenied",{reason:"Invalid trade target."});return;}
    const sameSpace=p.mode==="space"&&t.mode==="space"&&Math.hypot(p.x-t.x,p.y-t.y)<250;
    const samePlanet=p.mode==="planet"&&t.mode==="planet"&&p.planetId&&p.planetId===t.planetId&&Math.hypot((p.planetX||0)-(t.planetX||0),(p.planetY||0)-(t.planetY||0))<120;
    if(!sameSpace&&!samePlanet){socket.emit("tradeDenied",{reason:"Move closer to trade."});return;}
    t.pendingTradeFrom=p.id;t.pendingTradeAt=Date.now();
    io.to(t.id).emit("tradeRequest",{fromId:p.id,fromName:p.name,mode:p.mode});
    socket.emit("tradeRequestSent",{targetId:t.id,targetName:t.name});
  });

  socket.on("tradeResponse",({targetId,accepted})=>{
    const p=players.get(socket.id),t=players.get(targetId);if(!p||!t)return;
    if(p.pendingTradeFrom!==t.id||Date.now()-(p.pendingTradeAt||0)>25000){socket.emit("tradeDenied",{reason:"No active trade request."});return;}
    p.pendingTradeFrom=null;p.pendingTradeAt=0;
    io.to(t.id).emit("tradeResponse",{fromId:p.id,fromName:p.name,accepted:!!accepted});
    socket.emit("tradeResponse",{fromId:t.id,fromName:t.name,accepted:!!accepted});
    if(accepted)startTrade(t.id,p.id);
  });

  socket.on("tradeUpdate",({tradeId,offer})=>{
    const p=players.get(socket.id),s=tradeSessions.get(tradeId);if(!p||!s)return;
    const side=sideOfTrade(s,p.id);if(!side)return;
    const clean=sanitizeTradeOffer(offer,p);
    if(!validateTradeItems(p,clean.items)){socket.emit("tradeDenied",{reason:"You do not have those items in your server inventory."});return;}
    const changed=!tradeOffersEqual(s.offers[side],clean);
    s.offers[side]=clean;
    if(changed){s.ready.a=false;s.ready.b=false;}
    emitTradeState(s);
  });

  socket.on("tradeReady",({tradeId,ready,offer})=>{
    const p=players.get(socket.id),s=tradeSessions.get(tradeId);if(!p||!s)return;
    const side=sideOfTrade(s,p.id);if(!side)return;
    const other=side==="a"?"b":"a";
    const clean=sanitizeTradeOffer(offer||s.offers[side],p);
    if(!validateTradeItems(p,clean.items)){socket.emit("tradeDenied",{reason:"You do not have those items in your server inventory."});return;}
    const changed=!tradeOffersEqual(s.offers[side],clean);
    s.offers[side]=clean;
    if(changed)s.ready[other]=false;
    s.ready[side]=!!ready;
    if(s.ready.a&&s.ready.b)completeTrade(s);else emitTradeState(s);
  });

  socket.on("tradeCancel",({tradeId})=>{
    const p=players.get(socket.id),s=tradeSessions.get(tradeId);if(!p||!s)return;
    if(!sideOfTrade(s,p.id))return;
    cancelTrade(s,`${p.name} cancelled the trade.`);
  });


  /* Party events */
  socket.on("partyCreate",()=>{const p=players.get(socket.id);if(!p)return;const party=getOrCreatePartyForLeader(p);socket.emit("partyState",makePartyState(party.id));});
  socket.on("partyInvite",({targetId})=>{const p=players.get(socket.id),t=players.get(targetId);if(!p||!t||p.id===t.id){socket.emit("partyDenied",{reason:"Invalid party target."});return;}const party=getOrCreatePartyForLeader(p);if(party.leaderId!==p.id){socket.emit("partyDenied",{reason:"Only the party leader can invite."});return;}if(party.members.size>=PARTY_MAX_MEMBERS){socket.emit("partyDenied",{reason:"Party is full."});return;}if(t.partyId){socket.emit("partyDenied",{reason:"That player is already in a party."});return;}if(!nearbyForInvite(p,t)){socket.emit("partyDenied",{reason:"Move closer to invite that player."});return;}party.invites.set(t.id,{fromId:p.id,expires:Date.now()+30000});io.to(t.id).emit("partyInvite",{partyId:party.id,fromId:p.id,fromName:p.name});socket.emit("partyInviteSent",{targetName:t.name});emitPartyState(party.id);});
  socket.on("partyInviteResponse",({partyId,accepted})=>{const p=players.get(socket.id);const party=parties.get(partyId);if(!p||!party)return;const inv=party.invites.get(p.id);if(!inv||Date.now()>inv.expires){socket.emit("partyDenied",{reason:"Party invite expired."});return;}party.invites.delete(p.id);if(!accepted){io.to(inv.fromId).emit("partyDenied",{reason:`${p.name} declined the party invite.`});return;}if(p.partyId){socket.emit("partyDenied",{reason:"You are already in a party."});return;}if(party.members.size>=PARTY_MAX_MEMBERS){socket.emit("partyDenied",{reason:"Party is full."});return;}party.members.add(p.id);p.partyId=party.id;emitPartyState(party.id);broadcastChat("Party",`${p.name} joined a party.`,"#78ff8a");});
  socket.on("partyLeave",()=>{leaveParty(socket.id,"You left the party.");});
  socket.on("partyKick",({targetId})=>{const p=players.get(socket.id),t=players.get(targetId);if(!p?.partyId||!t||p.partyId!==t.partyId)return;const party=parties.get(p.partyId);if(!party||party.leaderId!==p.id)return;if(t.id===p.id)return;leaveParty(t.id,`Kicked from party by ${p.name}.`);emitPartyState(party.id);});
  socket.on("partyDisband",()=>{const p=players.get(socket.id);if(!p?.partyId)return;const party=parties.get(p.partyId);if(!party||party.leaderId!==p.id)return;for(const id of [...party.members]){const m=players.get(id);if(m)m.partyId=null;io.to(id).emit("partyLeft",{reason:"Party disbanded."});}parties.delete(party.id);});
  socket.on("requestPartyState",()=>{const p=players.get(socket.id);if(p?.partyId)socket.emit("partyState",makePartyState(p.partyId));});

  /* Faction events */
  socket.on("factionCreate",({name,tag,icon,color,description})=>{const p=players.get(socket.id);if(!p)return;if(p.factionId){socket.emit("factionDenied",{reason:"You are already in a faction."});return;}if((p.credits||0)<FACTION_CREATE_COST){socket.emit("factionDenied",{reason:`Need ${FACTION_CREATE_COST} credits to create a faction.`});return;}name=safeText(name,32)||`${p.name}'s Faction`;tag=safeText(tag,5).toUpperCase()||"NEW";icon=safeText(icon,4)||"⭐";color=safeText(color,16)||"#7be6ff";description=safeText(description,180)||"A new Space Eco faction.";if([...factions.values()].some(f=>f.tag.toLowerCase()===tag.toLowerCase())){socket.emit("factionDenied",{reason:"Faction tag already taken."});return;}p.credits-=FACTION_CREATE_COST;const id=`fac_${Date.now()}_${factionSeq++}`;const f={id,name,tag,icon,color,description,leaderId:p.id,level:1,xp:0,members:new Set([p.id]),memberMeta:{[p.id]:{name:p.name,role:"leader",rank:"Founder",contribution:0}},invites:new Map(),createdAt:Date.now(),quests:[],questResetAt:0};factions.set(id,f);p.factionId=id;p.factionRank="Founder";makeFactionQuests(f);socket.emit("creditUpdate",{credits:p.credits});emitFactionState(id);broadcastChat("Faction",`${p.name} founded [${tag}] ${name}!`,color);});
  socket.on("factionInvite",({targetId})=>{const p=players.get(socket.id),t=players.get(targetId);if(!p?.factionId||!t)return;const f=factions.get(p.factionId);if(!f||!canManageFaction(f,p.id)){socket.emit("factionDenied",{reason:"Only faction leaders/admins can invite."});return;}if(t.factionId){socket.emit("factionDenied",{reason:"That player is already in a faction."});return;}if(f.members.size>=factionCapacity(f)){socket.emit("factionDenied",{reason:"Faction is full."});return;}if(!nearbyForInvite(p,t)){socket.emit("factionDenied",{reason:"Move closer to invite that player."});return;}f.invites.set(t.id,{fromId:p.id,expires:Date.now()+45000});io.to(t.id).emit("factionInvite",{factionId:f.id,fromId:p.id,fromName:p.name,name:f.name,tag:f.tag,icon:f.icon,color:f.color});socket.emit("factionNotice",{message:`Faction invite sent to ${t.name}.`});});
  socket.on("factionInviteResponse",({factionId,accepted})=>{const p=players.get(socket.id),f=factions.get(factionId);if(!p||!f)return;const inv=f.invites.get(p.id);if(!inv||Date.now()>inv.expires){socket.emit("factionDenied",{reason:"Faction invite expired."});return;}f.invites.delete(p.id);if(!accepted){io.to(inv.fromId).emit("factionNotice",{message:`${p.name} declined the faction invite.`});return;}if(p.factionId){socket.emit("factionDenied",{reason:"You are already in a faction."});return;}if(f.members.size>=factionCapacity(f)){socket.emit("factionDenied",{reason:"Faction is full."});return;}f.members.add(p.id);f.memberMeta[p.id]={name:p.name,role:"member",rank:"Member",contribution:0};p.factionId=f.id;p.factionRank="Member";emitFactionState(f.id);broadcastChat("Faction",`${p.name} joined [${f.tag}] ${f.name}.`,f.color);});
  socket.on("factionLeave",()=>{const p=players.get(socket.id);if(!p?.factionId)return;const f=factions.get(p.factionId);if(!f)return;if(f.leaderId===p.id){socket.emit("factionDenied",{reason:"Leader must disband or transfer leadership first."});return;}f.members.delete(p.id);delete f.memberMeta[p.id];p.factionId=null;p.factionRank="member";socket.emit("factionLeft",{reason:"You left the faction."});emitFactionState(f.id);});
  socket.on("factionKick",({targetId})=>{const p=players.get(socket.id),t=players.get(targetId);if(!p?.factionId||!t||p.factionId!==t.factionId)return;const f=factions.get(p.factionId);if(!f||!canManageFaction(f,p.id)||targetId===f.leaderId)return;f.members.delete(t.id);delete f.memberMeta[t.id];t.factionId=null;t.factionRank="member";io.to(t.id).emit("factionLeft",{reason:`Kicked from faction by ${p.name}.`});emitFactionState(f.id);});
  socket.on("factionDisband",()=>{const p=players.get(socket.id);if(!p?.factionId)return;const f=factions.get(p.factionId);if(!f||f.leaderId!==p.id)return;for(const id of [...f.members]){const m=players.get(id);if(m){m.factionId=null;m.factionRank="member";}io.to(id).emit("factionLeft",{reason:"Faction disbanded."});}factions.delete(f.id);broadcastChat("Faction",`${f.name} has disbanded.`,"#ff8844");});
  socket.on("factionUpdate",({name,tag,icon,color,description})=>{const p=players.get(socket.id);if(!p?.factionId)return;const f=factions.get(p.factionId);if(!f||!canManageFaction(f,p.id))return;if(name)f.name=safeText(name,32);if(tag)f.tag=safeText(tag,5).toUpperCase();if(icon)f.icon=safeText(icon,4);if(color)f.color=safeText(color,16);if(description!==undefined)f.description=safeText(description,180);emitFactionState(f.id);});
  socket.on("factionSetRank",({targetId,role,rank})=>{const p=players.get(socket.id);if(!p?.factionId)return;const f=factions.get(p.factionId);if(!f||f.leaderId!==p.id||!f.members.has(targetId))return;if(targetId===f.leaderId)return;role=(role==="admin")?"admin":"member";f.memberMeta[targetId].role=role;f.memberMeta[targetId].rank=safeText(rank,24)|| (role==="admin"?"Admin":"Member");emitFactionState(f.id);});
  socket.on("factionAcceptQuest",({questId})=>{const p=players.get(socket.id);if(!p?.factionId)return;const f=factions.get(p.factionId);if(!f)return;ensureFactionQuests(f);const q=f.quests.find(q=>q.id===questId);if(!q||q.completed){socket.emit("factionDenied",{reason:"Quest unavailable."});return;}if(q.acceptedBy&&q.acceptedBy!==p.id){socket.emit("factionDenied",{reason:"Another member already accepted that quest."});return;}q.acceptedBy=p.id;q.acceptedByName=p.name;p.activeFactionQuestId=q.id;emitFactionState(f.id);});
  socket.on("requestFactionState",()=>{const p=players.get(socket.id);if(p?.factionId)socket.emit("factionState",makeFactionState(p.factionId,p.id));else socket.emit("factionState",null);});

  socket.on("oxygenDamage",({damage})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="planet")return;
    const dmg=planetDamageAfterModules(p,Math.max(1,Math.min(30,Number(damage)||7)));
    p.hp=Math.max(0,p.hp-dmg);
    socket.emit("oxygenDamageUpdate",{hp:p.hp,damage:Math.round(dmg)});
    if(p.hp<=0){
      p.deaths=(p.deaths||0)+1;
      socket.emit("youDied",{killedBy:"Oxygen Depletion"});
      setTimeout(()=>{const rp=players.get(socket.id);if(!rp)return;const sp=computeSpawnPoint();rp.mode="space";rp.planetId=null;refreshPlanetSuitStats(rp);rp.x=sp.x;rp.y=sp.y;rp.hp=rp.maxHp;rp.shield=rp.maxShield;rp.energy=100;socket.emit("respawn",{x:rp.x,y:rp.y});},3000);
    }
  });

  socket.on("planetNpcDamage",({damage,source})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="planet")return;
    const dmg=planetDamageAfterModules(p,Math.max(1,Math.min(30,Number(damage)||7)));
    p.hp=Math.max(0,p.hp-dmg);
    const attackerName=safeText(source||"Planet NPC",40);
    socket.emit("planetHit",{damage:dmg,hp:p.hp,attackerName});
    if(p.hp<=0){
      p.deaths=(p.deaths||0)+1;
      socket.emit("youDied",{killedBy:attackerName});
      io.emit("playerKilled",{victimId:p.id,victimName:p.name,killerId:null,killerName:attackerName});
      setTimeout(()=>{const rp=players.get(socket.id);if(!rp)return;const sp=computeSpawnPoint();rp.mode="space";rp.planetId=null;refreshPlanetSuitStats(rp);rp.x=sp.x;rp.y=sp.y;rp.hp=rp.maxHp;rp.shield=rp.maxShield;rp.energy=100;socket.emit("respawn",{x:rp.x,y:rp.y});},3000);
      broadcastLeaderboard();
    }
  });

  socket.on("requestInventorySync",()=>{const p=players.get(socket.id);if(p)emitInventorySync(p,"requested");});


  socket.on("storyProgressUpdate",({storyProgress})=>{
    const p=players.get(socket.id);if(!p)return;const incoming=normalizeStoryProgress(storyProgress||{}),cur=normalizeStoryProgress(p.storyProgress||{});
    p.storyProgress=normalizeStoryProgress({completed:Math.max(cur.completed,incoming.completed),startedAt:Math.min(cur.startedAt,incoming.startedAt),updatedAt:Math.max(cur.updatedAt,incoming.updatedAt)});
    socket.emit("storyProgressSync",{storyProgress:p.storyProgress});persistPlayerSoon(p,"story_progress",400);
  });

  socket.on("buyInventorySlot",()=>{
    const p=players.get(socket.id);if(!p)return;
    const SLOT_COST=1000,MAX_TOTAL_SLOTS=96;
    if((p.maxSlots||24)>=MAX_TOTAL_SLOTS){socket.emit("inventorySlotDenied",{reason:"Maximum slots reached."});return;}
    if((p.credits||0)<SLOT_COST){socket.emit("inventorySlotDenied",{reason:`Need ${SLOT_COST}cr.`});return;}
    p.credits-=SLOT_COST;p.maxSlots=(p.maxSlots||24)+1;p.invSlots.push({type:null,count:0});
    socket.emit("inventorySlotConfirm",{credits:p.credits,maxSlots:p.maxSlots});syncAndPersist(p,"buy_inventory_slot");
  });

  socket.on("sell",({requestId,resourceType,quantity})=>{
    const p=players.get(socket.id);requestId=String(requestId||"").slice(0,80);resourceType=String(resourceType||"");quantity=Math.floor(Number(quantity)||0);
    const deny=reason=>socket.emit("sellDenied",{requestId,reason});
    if(!p){return;}if(!isKnownResourceKey(resourceType)){deny("Unknown item. Resource catalog is out of sync.");return;}if(quantity<=0||quantity>500){deny("Invalid quantity.");return;}
    const pr=economy.price(resourceType);if(!pr){deny("This item cannot be sold here.");return;}
    if(!removeInventory(p,resourceType,quantity)){deny("You do not have that quantity in your server inventory.");return;}
    const earned=pr*quantity;p.credits+=earned;p.tradingVolume=(p.tradingVolume||0)+earned;economy.sold(resourceType,quantity);addScore(p,Math.floor(earned*0.1),"Trade");
    socket.emit("sellConfirm",{requestId,resourceType,quantity,earned,credits:p.credits,prices:economy.snapshot(),invSlots:p.invSlots,maxSlots:p.maxSlots});syncAndPersist(p,"sell_resource");
  });

  socket.on("buy",({requestId,resourceType,quantity,pricePerUnit,stationId})=>{
    const p=players.get(socket.id);requestId=String(requestId||"").slice(0,80);resourceType=String(resourceType||"");quantity=Math.floor(Number(quantity)||0);stationId=safeZoneId(stationId);
    const deny=(reason,extra={})=>socket.emit("buyDenied",{requestId,resourceType,reason,...extra});
    if(!p)return;if(!isKnownResourceKey(resourceType)){deny("Unknown item. Resource catalog is out of sync.",{resourceCatalogVersion:2});return;}if(quantity<=0||quantity>500){deny("Invalid quantity.");return;}
    const marketPrice=Math.max(1,economy.price(resourceType)||1),quotedPrice=Math.floor(Number(pricePerUnit)||0);
    let civSale=null;
    if(stationId){
      for(const zone of civilizationZones.values()){
        ensureCivLogistics(zone);
        const station=[...(zone.baseStations||[]),...(zone.builtStations||[])].find(st=>st.id===stationId);
        if(!station)continue;
        const listing=station.market?.[resourceType];
        if(!listing||Number(listing.amount||0)<quantity){deny("That civilization station does not have enough assigned stock.");return;}
        civSale={zone,station,listing};break;
      }
    }
    const minAllowed=Math.max(1,Math.ceil(marketPrice*1.01)),maxAllowed=Math.max(minAllowed,Math.ceil(marketPrice*6));
    if(quotedPrice<=0){deny("Price unavailable. Retry.",{pricePerUnit:civSale?civSale.listing.price:minAllowed});return;}
    if(civSale&&quotedPrice!==Math.floor(Number(civSale.listing.price)||0)){deny("Station price refreshed — retry purchase.",{pricePerUnit:civSale.listing.price});return;}
    if(!civSale&&(quotedPrice<minAllowed||quotedPrice>maxAllowed)){deny("Station price refreshed — retry purchase.",{pricePerUnit:minAllowed});return;}
    const unitPrice=civSale?Math.floor(Number(civSale.listing.price)||0):quotedPrice,cost=unitPrice*quantity;if((p.credits||0)<cost){deny("Insufficient credits.",{pricePerUnit:unitPrice});return;}
    if(!canFitInventory(p,resourceType,quantity)){deny("Inventory full.",{pricePerUnit:unitPrice});return;}
    p.credits-=cost;economy.bought(resourceType,quantity);if(!addInventory(p,resourceType,quantity)){p.credits+=cost;deny("Inventory changed before purchase completed.",{pricePerUnit:unitPrice});return;}
    if(civSale){
      civSale.listing.amount-=quantity;if(civSale.listing.amount<=0)delete civSale.station.market[resourceType];
      civSale.zone.bankCredits=(civSale.zone.bankCredits||0)+cost;
      const owner=players.get(civSale.zone.ownerId);
      if(owner){io.to(owner.id).emit("civilizationSaleRecorded",{zoneId:civSale.zone.zoneId,stationId:civSale.station.id,resourceType,quantity,amount:cost,bankCredits:civSale.zone.bankCredits,buyerName:p.name});persistPlayerSoon(owner,"civilization_station_sale");}
      broadcastCivilizationZonesList();
    }
    socket.emit("buyConfirm",{requestId,resourceType,quantity,unitPrice,cost,credits:p.credits,prices:economy.snapshot(),invSlots:p.invSlots,maxSlots:p.maxSlots,civilizationSale:!!civSale});syncAndPersist(p,civSale?"civilization_station_purchase":"buy_resource");
  });

  socket.on("buyShip",({shipTypeKey})=>{
    const p=players.get(socket.id);if(!p)return;
    const def=SHIP_TYPES[shipTypeKey];
    if(!def){socket.emit("shipBuyDenied",{reason:"Unknown ship."});return;}
    if(def.craftOnly||def.recipe){socket.emit("shipBuyDenied",{reason:"This ship must be crafted from parts."});return;}
    if(p.shipType===shipTypeKey){socket.emit("shipBuyDenied",{reason:"Already own this ship."});return;}
    if(p.credits<def.price){socket.emit("shipBuyDenied",{reason:`Need ${def.price}cr.`});return;}
    p.credits-=def.price;p.shipType=shipTypeKey;applyShipStats(p,true);
    socket.emit("shipBuyConfirm",{shipTypeKey,credits:p.credits,hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield,equippedAttachments:normalizeAttachments(p.equippedAttachments||{})});
    syncAndPersist(p,"buy_ship");
    broadcastChat("Server",`${p.name} upgraded to a ${def.name}!`,"#ffdd44");
  });

  socket.on("craftShip",({shipTypeKey})=>{
    const p=players.get(socket.id);if(!p)return;
    shipTypeKey=String(shipTypeKey||"");
    const def=SHIP_TYPES[shipTypeKey];
    if(!def||!def.recipe){socket.emit("craftShipDenied",{reason:"Unknown craftable ship."});return;}
    if(p.shipType===shipTypeKey){socket.emit("craftShipDenied",{reason:"Already flying this ship."});return;}
    const check=canCraftRecipe(p,def.recipe);
    if(!check.ok){socket.emit("craftShipDenied",{reason:check.reason||"Missing parts."});return;}
    consumeCraftRecipe(p,def.recipe);
    p.shipType=shipTypeKey;applyShipStats(p,true);
    socket.emit("craftShipConfirm",{shipTypeKey,credits:p.credits,hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield,invSlots:p.invSlots,maxSlots:p.maxSlots,equippedAttachments:normalizeAttachments(p.equippedAttachments||{})});
    syncAndPersist(p,"craft_ship");
    broadcastChat("Server",`${p.name} crafted a ${def.name}!`,"#ffdd44");
  });

  socket.on("stationQuestReward",({questId,rewardCredits,rewardXp,parts})=>{
    const p=players.get(socket.id);if(!p)return;
    const items=[];
    for(const it of Array.isArray(parts)?parts:[]){items.push({type:String(it.type||""),qty:Math.max(1,Math.min(12,Math.floor(Number(it.qty)||1)))});}
    const bundle=grantRewardBundle(p,{credits:Math.min(50000,Math.floor(Number(rewardCredits)||0)),xp:Math.min(15000,Math.floor(Number(rewardXp)||0)),items},"Station Quest");
    if(!bundle.ok){socket.emit("stationQuestRewardDenied",{questId,reason:bundle.reason});return;}
    socket.emit("stationQuestRewardConfirm",{questId,credits:p.credits,invSlots:p.invSlots,maxSlots:p.maxSlots,reward:bundle});
    syncAndPersist(p,"station_quest_reward");
  });

  socket.on("shipPartReward",({items,credits,xp,reason})=>{
    const p=players.get(socket.id);if(!p)return;
    const bundle=grantRewardBundle(p,{credits:Math.min(25000,Math.floor(Number(credits)||0)),xp:Math.min(8000,Math.floor(Number(xp)||0)),items:Array.isArray(items)?items:[]},safeText(reason||"Salvage",40));
    if(!bundle.ok){socket.emit("shipPartRewardDenied",{reason:bundle.reason});return;}
    socket.emit("shipPartRewardConfirm",{credits:p.credits,invSlots:p.invSlots,maxSlots:p.maxSlots,reward:bundle,reason:safeText(reason||"Salvage",40)});
    syncAndPersist(p,"ship_part_reward");
  });

  socket.on("spaceLootPickup",({claimId,resourceType,type,x,y})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="space")return;
    const kind=String(resourceType||type||"");claimId=String(claimId||"").slice(0,80);
    if(!RES_KEYS.includes(kind)){socket.emit("spaceLootPickupDenied",{claimId,resourceType:kind,reason:"Unknown loot type."});return;}
    const now=Date.now();
    p._spaceLootPickups=(p._spaceLootPickups||[]).filter(t=>now-t<2500);
    if(p._lastSpaceLootPickupAt&&now-p._lastSpaceLootPickupAt<65){socket.emit("spaceLootPickupDenied",{claimId,resourceType:kind,reason:"Pickup too fast."});return;}
    if(p._spaceLootPickups.length>28){socket.emit("spaceLootPickupDenied",{claimId,resourceType:kind,reason:"Too many pickups at once."});return;}
    const lx=Number(x),ly=Number(y);
    if(Number.isFinite(lx)&&Number.isFinite(ly)&&Math.hypot(p.x-lx,p.y-ly)>420){socket.emit("spaceLootPickupDenied",{claimId,resourceType:kind,reason:"Move closer to the loot."});return;}
    if(!canFitInventory(p,kind,1)){socket.emit("spaceLootPickupDenied",{claimId,resourceType:kind,reason:"Inventory full."});return;}
    p._lastSpaceLootPickupAt=now;p._spaceLootPickups.push(now);
    addInventory(p,kind,1);
    socket.emit("spaceLootPickupConfirm",{claimId,resourceType:kind,quantity:1,credits:p.credits,invSlots:p.invSlots,maxSlots:p.maxSlots});
    syncAndPersist(p,"space_loot_pickup");
  });


  socket.on("claimBadgeReward",({badgeId,name})=>{
    const p=players.get(socket.id);if(!p)return;
    badgeId=safeText(badgeId||"badge",48);
    name=safeText(name||"Badge",48);
    p.badgeRewards=p.badgeRewards||{};
    if(p.badgeRewards[badgeId]){socket.emit("badgeRewardDenied",{badgeId,reason:"Badge reward already claimed."});return;}
    const rewardTable={
      first_quest:{credits:1200,xp:300},
      contract_captain:{credits:8000,xp:1800},
      pirate_breaker:{credits:7000,xp:1600},
      salvage_runner:{credits:6500,xp:1500},
      shipwright:{credits:10000,xp:2200},
      first_boarding:{credits:2500,xp:650},
      first_rescue:{credits:3000,xp:750}
    };
    const reward=rewardTable[badgeId]||{credits:1800,xp:450};
    const bundle=grantRewardBundle(p,{credits:reward.credits,xp:reward.xp,items:[]},"Badge Reward");
    if(!bundle.ok){socket.emit("badgeRewardDenied",{badgeId,reason:bundle.reason||"Badge reward failed."});return;}
    p.badgeRewards[badgeId]=Date.now();
    socket.emit("badgeRewardConfirm",{badgeId,name,credits:p.credits,xp:p.xp,level:p.level,reward:bundle});
    syncAndPersist(p,"badge_reward");
  });

  socket.on("requestCivilizationZones",()=>{emitCivilizationZones(socket);});

  socket.on("buyCivilizationZone",(raw)=>{
    const p=players.get(socket.id);if(!p||p.mode!=="space")return;
    const input=safeCivZoneInput(raw);if(!input){socket.emit("civilizationZoneDenied",{reason:"Invalid civilization zone."});return;}
    if(Math.hypot(p.x-input.x,p.y-input.y)>520){socket.emit("civilizationZoneDenied",{zoneId:input.zoneId,reason:"Move closer to the super station."});return;}
    let zone=civilizationZones.get(input.zoneId);
    if(zone?.ownerId||zone?.ownerMemberId){socket.emit("civilizationZoneDenied",{zoneId:input.zoneId,reason:`${zone.ownerName||"Another player"} already owns this civilization zone.`});return;}
    const cost=civilizationZonePurchaseCost(input);
    if((p.credits||0)<cost){socket.emit("civilizationZoneDenied",{zoneId:input.zoneId,reason:`Need ${cost}cr to buy this zone.`,cost});return;}
    p.credits-=cost;
    zone=makeCivilizationZoneRecord(input,p);
    civilizationZones.set(input.zoneId,zone);
    // A zone can be purchased while a client-side retaliation was already in
    // flight. Clear only reciprocal/automatic war orders between zones that
    // now share this owner; an explicit player-issued attack remains intact.
    clearAutomaticCivilizationWarsForOwner(p);
    addScore(p,2500,"Civilization Acquired");
    socket.emit("civilizationZoneBought",{zone:publicCivilizationZone(zone,p.id),credits:p.credits,cost});
    socket.emit("creditUpdate",{credits:p.credits});
    broadcastCivilizationZonesList();
    broadcastChat("Server",`${p.name} purchased ${zone.name} for ${cost}cr and now collects station taxes there!`,zone.color||"#ffdd44");
    persistPlayerSoon(p,"buy_civilization_zone");
  });

  // Player-founded zones deliberately have no inherited stations, turrets, or
  // free ships.  They use the same authoritative logistics record as a bought
  // zone, so every future station/turret/menu feature works without a second
  // ownership system.
  socket.on("buildCivilizationZone",raw=>{
    const p=players.get(socket.id);if(!p||p.mode!=="space")return;
    const x=Math.round(Number(raw?.x)),y=Math.round(Number(raw?.y));
    if(!Number.isFinite(x)||!Number.isFinite(y)||Math.hypot(p.x-x,p.y-y)>260){socket.emit("civilizationZoneDenied",{reason:"Choose a build point near your ship."});return;}
    const radius=420,cost=1000000;
    if((p.credits||0)<cost){socket.emit("civilizationZoneDenied",{reason:"Need 1,000,000cr to found a civilization zone."});return;}
    const rimConflict=civilizationRimPlacementConflict(x,y,radius);
    if(rimConflict){socket.emit("civilizationZoneDenied",{reason:"A civilization rim would touch or overlap this location."});return;}
    const zoneId=`playerciv_${String(p.memberId||p.id).replace(/[^a-zA-Z0-9]/g,"").slice(-18)}_${Date.now().toString(36)}`;
    const faction=civFactionFor(zoneId),zone={...civZoneDefaults({zoneId,zoneLevel:6}),zoneId,name:`${p.name}'s Frontier`,color:faction.color,x,y,radius,baseStationCount:0,superStationLevel:6,zoneLevel:6,ownerId:p.id,ownerMemberId:p.memberId||null,ownerName:p.name,purchasedAt:Date.now(),baseStations:[],builtStations:[],stationTasks:{},pendingTax:0,totalTaxCollected:0,playerFounded:true,stationTierCosmetics:{},npcshipCosmeticKey:null,turretCosmeticKey:null};
    ensureCivLogistics(zone);p.credits-=cost;civilizationZones.set(zoneId,zone);clearAutomaticCivilizationWarsForOwner(p);addScore(p,5000,"Civilization Founded");
    socket.emit("civilizationZoneBuilt",{zone:publicCivilizationZone(zone,p.id),credits:p.credits,cost});socket.emit("creditUpdate",{credits:p.credits});broadcastCivilizationZonesList();persistPlayerSoon(p,"build_civilization_zone");
  });

  socket.on("buildCivilizationStation",(raw={})=>{
    let {zoneId,tier}=raw||{};
    const p=players.get(socket.id);if(!p||p.mode!=="space")return;
    zoneId=safeZoneId(zoneId);tier=String(tier||"");
    const zone=civilizationZones.get(zoneId);if(!zone||!playerOwnsCivilizationZone(p,zone)){socket.emit("civilizationZoneDenied",{zoneId,reason:"You do not own this civilization zone."});return;}zone.ownerId=p.id;zone.ownerName=p.name;
    if(!CIV_STATION_TIERS[tier]){socket.emit("civilizationZoneDenied",{zoneId,reason:"Unknown station tier."});return;}
    dedupeCivilizationBuiltStations(zone);
    if(Math.hypot(p.x-zone.x,p.y-zone.y)>620){socket.emit("civilizationZoneDenied",{zoneId,reason:"Build from the central super station."});return;}
    if((zone.builtStations||[]).length>=30){socket.emit("civilizationZoneDenied",{zoneId,reason:"This civilization zone is fully built out."});return;}
    const buildLockKey=`${p.id}|${zoneId}|${tier}`;
    const now=Date.now();
    if(civilizationBuildLocks.get(buildLockKey)>now){socket.emit("civilizationZoneDenied",{zoneId,reason:"Build request already processing."});return;}
    civilizationBuildLocks.set(buildLockKey,now+900);
    const cost=civilizationZoneStationBuildCost(zone,tier);
    if((p.credits||0)<cost){socket.emit("civilizationZoneDenied",{zoneId,reason:`Need ${cost}cr to build a ${CIV_STATION_TIERS[tier].name} station.`,cost});return;}
    p.credits-=cost;
    const pt=randomPointInZone(zone,tier);
    const station={id:`${zone.zoneId}|ownedciv|${zone.builtStations.length}_${Date.now()}`,x:pt.x,y:pt.y,tier,ownerName:p.name,createdAt:Date.now()};
    zone.builtStations.push(station);
    zone.stationTasks=zone.stationTasks||{};zone.stationTasks[station.id]={task:"mine",targetZoneId:null,updatedAt:Date.now()};
    addScore(p,800,"Civilization Station Built");
    socket.emit("civilizationStationBuilt",{zone:publicCivilizationZone(zone,p.id),station,credits:p.credits,cost});
    socket.emit("creditUpdate",{credits:p.credits});
    broadcastCivilizationZonesList();
    broadcastChat("Server",`${p.name} expanded ${zone.name} with a ${CIV_STATION_TIERS[tier].name} station.`,zone.color||"#ffdd44");
    persistPlayerSoon(p,"build_civilization_station");
  });

  // ── V4.1 owned civilization station / super-station logistics ──
  function ownCivZone(raw){const p=players.get(socket.id),zone=civilizationZones.get(safeZoneId(raw?.zoneId));if(!p||!zone||!playerOwnsCivilizationZone(p,zone))return {p:null,zone:null};ensureCivLogistics(zone);zone.ownerId=p.id;zone.ownerName=p.name;return {p,zone};}
  function civStation(zone,id){const key=safeZoneId(id);return civAllStations(zone).find(s=>s.id===key)||null;}
  function civSync(p,zone,reason){socket.emit("civilizationLogisticsSync",{zone:publicCivilizationZone(zone,p.id),reason});emitInventorySync(p,"requested");broadcastCivilizationZonesList();persistPlayerSoon(p,reason);}
  socket.on("requestCivilizationLogistics",raw=>{const {p,zone}=ownCivZone(raw);if(p&&zone)civSync(p,zone,"civ_logistics_view");});
  socket.on("buyCivilizationRosterShip",raw=>{const {p,zone}=ownCivZone(raw),st=zone&&civStation(zone,raw?.stationId),def=CIV_SHIP_CATALOG[String(raw?.shipKey||"")];if(!p||!zone||!st||!def){socket.emit("civilizationZoneDenied",{reason:"Invalid station ship request."});return;}if(st.destroyed){socket.emit("civilizationZoneDenied",{reason:"Destroyed stations cannot build ships."});return;}if((st.shipRoster||[]).length>=st.shipCapacity){socket.emit("civilizationZoneDenied",{reason:"This station has reached its ship capacity."});return;}const buildCost=Math.round(def.credits*(zone.factionId==="frontier"?.88:1)),check=civRecipeOk(p,def);if(!check.ok||p.credits<buildCost){socket.emit("civilizationZoneDenied",{reason:check.reason||`Need ${buildCost}cr.`});return;}p.credits-=buildCost;civConsumeRecipe(p,def);st.shipRoster.push({id:`${st.id}|${raw.shipKey}|${Date.now()}`,shipKey:raw.shipKey,name:def.name,role:def.role,sprite:def.sprite,status:"respawning",builtAt:Date.now(),respawnAt:Date.now()+civStationRespawnDelay(st),cargoBalanceVersion:CIV_CARGO_BALANCE_VERSION,stats:civFactionShipStats(zone,def)});socket.emit("creditUpdate",{credits:p.credits});civSync(p,zone,"civ_ship_built");});
  socket.on("upgradeCivilizationStation",raw=>{const {p,zone}=ownCivZone(raw),st=zone&&civStation(zone,raw?.stationId),stat=String(raw?.stat||"");if(!p||!st||!["capacity","health","shield","respawn"].includes(stat)){socket.emit("civilizationZoneDenied",{reason:"Invalid station upgrade."});return;}if(st.destroyed){socket.emit("civilizationZoneDenied",{reason:"Destroyed stations cannot be upgraded."});return;}const respawn=stat==="respawn",lv=respawn?Math.max(1,Number(st.respawnLevel||0)+1):Math.max(1,Number(st.level)||1),cost=(respawn?12000:8000)*lv,res=respawn?"engine_core":stat==="capacity"?"cargo_pod":stat==="health"?"hull_plate":"shield_matrix";if(p.credits<cost||inventoryCount(p,res)<lv){socket.emit("civilizationZoneDenied",{reason:`Need ${cost}cr and ${lv} ${res.replace(/_/g," ")}.`});return;}p.credits-=cost;removeInventory(p,res,lv);if(respawn)st.respawnLevel=Math.min(10,Number(st.respawnLevel||0)+1);else{st.level=lv+1;if(stat==="capacity")st.shipCapacity+=2;if(stat==="health"){st.maxHp+=650;st.hp=st.maxHp;}if(stat==="shield"){st.maxShield+=360;st.shield=st.maxShield;}}socket.emit("creditUpdate",{credits:p.credits});civSync(p,zone,"civ_station_upgrade");});
  socket.on("setCivilizationResourceTarget",raw=>{const {p,zone}=ownCivZone(raw),st=zone&&civStation(zone,raw?.stationId);if(!p||!st)return;if(st.destroyed){socket.emit("civilizationZoneDenied",{reason:"Destroyed stations cannot receive a mining assignment."});return;}const target=raw?.planet||{};const d=Math.hypot((Number(target.x)||0)-st.x,(Number(target.y)||0)-st.y);if(!target.id||d>Math.max(1500,zone.radius*4)){socket.emit("civilizationZoneDenied",{reason:"That resource planet is outside this station's logistics range."});return;}const assignment={id:String(target.id).slice(0,80),name:safeText(target.name||"Resource Planet",48),x:Math.round(target.x),y:Math.round(target.y),resources:Array.isArray(target.resources)?target.resources.slice(0,12):[],density:Math.max(0,Number(target.density)||0)};st.resourceTarget=assignment;zone.stationTasks[st.id]=civMineTask();if(!st.isSuperStation&&!zone.superStation?.resourceTarget)zone.superStation.resourceTarget={...assignment};civSync(p,zone,"civ_resource_target");});
  socket.on("civilizationRosterShipDestroyed",raw=>{const {p,zone}=ownCivZone(raw),st=zone&&civStation(zone,raw?.stationId),shipId=safeZoneId(raw?.shipId);if(!p||!st||st.destroyed||!shipId)return;const roster=(st.shipRoster||[]).find(sh=>sh.id===shipId);if(!roster||roster.status==="destroyed")return;roster.status="respawning";roster.respawnAt=Date.now()+civStationRespawnDelay(st);roster.destroyedAt=Date.now();civSync(p,zone,"civ_roster_ship_respawning");});
  socket.on("civilizationStationDestroyed",raw=>{const {p,zone}=ownCivZone(raw),st=zone&&civStation(zone,raw?.stationId);if(!p||!st||st.destroyed)return;st.destroyed=true;st.destroyedAt=Date.now();st.hp=0;st.shield=0;st.resourceRates={};st.miningCargo={};for(const roster of st.shipRoster||[]){roster.status="destroyed";roster.destroyedAt=Date.now();}civSync(p,zone,"civ_station_destroyed");});
  socket.on("civilizationStockpileTransfer",raw=>{const {p,zone}=ownCivZone(raw);if(!p||!zone)return;const type=String(raw?.type||"").slice(0,80),amount=Math.max(1,Math.floor(Number(raw?.amount)||1)),dir=raw?.direction;if(!type)return;if(dir==="deposit"){if(inventoryCount(p,type)<amount){socket.emit("civilizationZoneDenied",{reason:"You do not have that amount."});return;}const total=Object.values(zone.stockpile).reduce((a,b)=>a+Number(b||0),0);if(total+amount>zone.stockpileCapacity){socket.emit("civilizationZoneDenied",{reason:"Super station stockpile is full."});return;}removeInventory(p,type,amount);zone.stockpile[type]=(zone.stockpile[type]||0)+amount;}else if(dir==="withdraw"){if((zone.stockpile[type]||0)<amount||!canFitInventory(p,type,amount)){socket.emit("civilizationZoneDenied",{reason:"Cannot withdraw: unavailable stock or inventory full."});return;}civAddInventoryAny(p,type,amount);zone.stockpile[type]-=amount;}else return;civSync(p,zone,"civ_stockpile_transfer");});
  socket.on("civilizationBankTransfer",raw=>{const {p,zone}=ownCivZone(raw);if(!p||!zone)return;const amount=Math.max(1,Math.floor(Number(raw?.amount)||0));if(raw?.direction==="deposit"){if(p.credits<amount){socket.emit("civilizationZoneDenied",{reason:"Not enough personal credits."});return;}p.credits-=amount;zone.bankCredits+=amount;}else if(raw?.direction==="withdraw"){if(zone.bankCredits<amount){socket.emit("civilizationZoneDenied",{reason:"Not enough credits in the station bank."});return;}zone.bankCredits-=amount;p.credits+=amount;}else return;socket.emit("creditUpdate",{credits:p.credits});civSync(p,zone,"civ_bank_transfer");});
  socket.on("assignCivilizationMarketStock",raw=>{const {p,zone}=ownCivZone(raw);if(!p||!zone)return;const type=String(raw?.type||"").slice(0,80),amount=Math.max(1,Math.floor(Number(raw?.amount)||0)),price=Math.max(1,Math.floor(Number(raw?.price)||1));const ids=Array.isArray(raw?.stationIds)?raw.stationIds:[raw?.stationId];const targets=ids.map(id=>civStation(zone,id)).filter(Boolean);if(!type||!targets.length){socket.emit("civilizationZoneDenied",{reason:"Choose at least one valid civilization station."});return;}const reclaim=targets.reduce((n,st)=>n+Math.max(0,Math.floor(Number(st.market?.[type]?.amount)||0)),0);if((zone.stockpile[type]||0)+reclaim<amount*targets.length){socket.emit("civilizationZoneDenied",{reason:"Insufficient stockpile resources for that station assignment."});return;}for(const st of targets){const old=Math.max(0,Math.floor(Number(st.market?.[type]?.amount)||0));if(old){zone.stockpile[type]=(zone.stockpile[type]||0)+old;delete st.market[type];}}for(const st of targets){st.market[type]={amount,price};zone.stockpile[type]-=amount;}civSync(p,zone,"civ_market_assignment");});
  socket.on("removeCivilizationMarketStock",raw=>{const {p,zone}=ownCivZone(raw);if(!p||!zone)return;const type=String(raw?.type||"").slice(0,80);const ids=Array.isArray(raw?.stationIds)?raw.stationIds:[raw?.stationId];const targets=ids.map(id=>civStation(zone,id)).filter(Boolean);if(!type||!targets.length){socket.emit("civilizationZoneDenied",{reason:"Choose at least one station and listed item."});return;}let returned=0;for(const st of targets){const listing=st.market?.[type];if(!listing)continue;returned+=Math.max(0,Math.floor(Number(listing.amount)||0));delete st.market[type];}if(!returned){socket.emit("civilizationZoneDenied",{reason:"That item is not listed at the selected station."});return;}zone.stockpile[type]=(zone.stockpile[type]||0)+returned;civSync(p,zone,"civ_market_recalled");});
  socket.on("upgradeCivilizationZone",raw=>{const {p,zone}=ownCivZone(raw);if(!p||!zone)return;const lv=zone.zoneLevel||1;if(lv>=10){socket.emit("civilizationZoneDenied",{reason:"This civilization zone is already level 10."});return;}const cost=25000*lv,res=lv<4?"iron":lv<7?"crystal":"obelisk_core";if(p.credits<cost||inventoryCount(p,res)<lv){socket.emit("civilizationZoneDenied",{reason:`Need ${cost}cr and ${lv} ${res.replace(/_/g," ")}.`});return;}p.credits-=cost;removeInventory(p,res,lv);zone.zoneLevel=lv+1;zone.stockpileCapacity=Math.min(10000,1000+lv*1000);socket.emit("creditUpdate",{credits:p.credits});civSync(p,zone,"civ_zone_upgrade");});
  socket.on("buildCivilizationTurret",raw=>{const {p,zone}=ownCivZone(raw);if(!p||!zone)return;const key=String(raw?.turretKey||"pulse"),def=CIV_TURRET_CATALOG[key];if(!def){socket.emit("civilizationZoneDenied",{reason:"Unknown turret design."});return;}const cap=Math.min(20,2+(zone.zoneLevel||1)),built=(zone.turrets||[]).length,scaledCredits=Math.round(def.credits*(1+built*.08));if(built>=cap){socket.emit("civilizationZoneDenied",{reason:"Turret capacity reached."});return;}const recipeCheck=civRecipeOk(p,def);if(p.credits<scaledCredits||!recipeCheck.ok){socket.emit("civilizationZoneDenied",{reason:recipeCheck.reason||`Need ${scaledCredits}cr.`});return;}p.credits-=scaledCredits;civConsumeRecipe(p,def);const stats=civFactionTurretStats(zone,def),a=((built*2.399)+.3)%6.283;zone.turrets.push({id:`${zone.zoneId}|turret|${Date.now()}`,x:Math.round(zone.x+Math.cos(a)*(zone.radius-40)),y:Math.round(zone.y+Math.sin(a)*(zone.radius-40)),turretType:key,name:def.name,sprite:def.sprite,effect:def.effect,slow:def.slow||0,burn:def.burn||0,burnSeconds:def.burnSeconds||0,pierce:def.pierce||0,shieldBreak:def.shieldBreak||0,range:stats.range,hp:stats.hp,shield:stats.shield,maxHp:stats.hp,maxShield:stats.shield,damage:stats.damage,fireRate:stats.fireRate,cooldown:0,color:zone.color});socket.emit("creditUpdate",{credits:p.credits});civSync(p,zone,"civ_turret_build");});
  socket.on("offerCivilizationContract",raw=>{const {p,zone}=ownCivZone(raw);if(!p||!zone)return;const targetId=safeZoneId(raw?.targetZoneId);if(!targetId||targetId===zone.zoneId){socket.emit("civilizationZoneDenied",{reason:"Choose a nearby civilization zone."});return;}const target=civilizationZones.get(targetId);const credit=Math.max(0,Math.floor(Number(raw?.creditsPerMinute)||0)),giveType=String(raw?.giveType||""),giveAmount=Math.max(0,Math.floor(Number(raw?.giveAmount)||0));if(credit>zone.bankCredits||(giveType&&giveAmount>(zone.stockpile[giveType]||0))){socket.emit("civilizationZoneDenied",{reason:"Your super station cannot fund that contract."});return;}const fairness=Math.max(.1,Math.min(.95,.35+Math.min(.35,(credit+giveAmount*(RES_BASE[giveType]||1))/12000)+Math.min(.15,(zone.builtStations?.length||0)/30)));const contract={id:`contract_${Date.now()}`,targetZoneId:targetId,status:"pending",createdAt:Date.now(),decisionAt:Date.now()+120000,give:{credits:credit,type:giveType,amount:giveAmount},receive:{credits:Math.max(0,Math.floor(Number(raw?.receiveCredits)||0)),type:String(raw?.receiveType||""),amount:Math.max(0,Math.floor(Number(raw?.receiveAmount)||0))},fairness,deliveryCapacity:(zone.builtStations||[]).reduce((n,s)=>n+(s.shipRoster||[]).filter(x=>x.role==="trade").reduce((m,x)=>m+(x.stats?.capacity||0),0),0)};zone.contracts.push(contract);if(target){ensureCivLogistics(target);target.contracts.push({...contract,sourceZoneId:zone.zoneId,incoming:true});}civSync(p,zone,"civ_contract_offer");});
  socket.on("cancelCivilizationContract",raw=>{const {p,zone}=ownCivZone(raw);if(!p||!zone)return;const id=String(raw?.contractId||"").slice(0,100);const c=(zone.contracts||[]).find(x=>x.id===id&&!x.incoming);if(!c||c.status!=="pending"){socket.emit("civilizationZoneDenied",{reason:"Only a pending outgoing contract can be withdrawn."});return;}zone.contracts=zone.contracts.filter(x=>x.id!==id);const target=civilizationZones.get(c.targetZoneId);if(target)target.contracts=(target.contracts||[]).filter(x=>!(x.id===id&&x.sourceZoneId===zone.zoneId));civSync(p,zone,"civ_contract_cancel");});
  socket.on("setCivilizationRelation",raw=>{const {p,zone}=ownCivZone(raw);if(!p||!zone)return;const targetId=safeZoneId(raw?.targetZoneId),relation=raw?.relation==="enemy"?"enemy":"neutral";if(!targetId||targetId===zone.zoneId)return;zone.relations[targetId]=relation;if(relation==="enemy"){const target=civilizationZones.get(targetId);if(target)for(const st of civAllStations(zone))zone.stationTasks[st.id]=civAttackTask(target,false);}civSync(p,zone,"civ_relation");});

  socket.on("buyStation",({x,y,tier})=>{
    const p=players.get(socket.id);if(!p)return;
    const td=OWNED_STATION_TIERS[tier];if(!td){socket.emit("stationBuyDenied",{reason:"Unknown tier."});return;}
    if(p.credits<td.price){socket.emit("stationBuyDenied",{reason:`Need ${td.price}cr.`});return;}
    const key=`${Math.round(x/100)}_${Math.round(y/100)}`;
    if(ownedStations.has(key)){socket.emit("stationBuyDenied",{reason:"Location occupied."});return;}
    p.credits-=td.price;syncAndPersist(p,"buy_station");
    const st={key,ownerId:p.id,ownerMemberId:p.memberId||null,ownerName:p.name,x,y,tier,hiredShips:[],accumulatedGoods:{},createdAt:Date.now(),...makeStationState(tier)};
    ownedStations.set(key,st);addScore(p,1000,"Station Built");
    socket.emit("stationBuyConfirm",{key,x,y,tier,credits:p.credits});
    broadcastOwnedStationsList();persistPlayerSoon(p,"buy_station_buildings");
    broadcastChat("Server",`${p.name} built a ${td.name} at (${Math.round(x)}, ${Math.round(y)})!`,"#ffcc44");
  });

  socket.on("hireShip",({stationKey})=>{
    const p=players.get(socket.id);if(!p)return;
    const st=ownedStations.get(stationKey);if(!st||st.ownerId!==p.id){socket.emit("hireDenied",{reason:"Not your station."});return;}
    if(st.destroyed){socket.emit("hireDenied",{reason:"Station destroyed."});return;}
    const td=OWNED_STATION_TIERS[st.tier];
    if(st.hiredShips.length>=td.maxShips){socket.emit("hireDenied",{reason:`Max ${td.maxShips} ships.`});return;}
    if(p.credits<td.shipHireCost){socket.emit("hireDenied",{reason:`Need ${td.shipHireCost}cr.`});return;}
    p.credits-=td.shipHireCost;syncAndPersist(p,"hire_station_ship");
    st.hiredShips.push({id:`os_${stationKey}_${Date.now()}_${Math.floor(Math.random()*9999)}`,state:(Date.now()<(st.underAttackUntil||0)?"defending":"collecting"),cargo:{},createdAt:Date.now(),respawnAt:0});
    persistPlayerSoon(p,"hire_station_ship_building");
    socket.emit("hireConfirm",{stationKey,shipCount:st.hiredShips.length,credits:p.credits});
    socket.emit("creditUpdate",{credits:p.credits});
    broadcastOwnedStationsList();
  });

  socket.on("requestMercOffers",()=>{
    const p=players.get(socket.id);if(!p)return;
    const cat=generateMercOffersForPlayer(p);
    socket.emit("mercOffers",{offers:cat.offers,expires:cat.expires,activeMercs:(p.activeMercs||[]).map(publicMerc),maxActive:MAX_ACTIVE_MERCS});
  });

  socket.on("hireMerc",({offerId})=>{
    const p=players.get(socket.id);if(!p)return;
    p.activeMercs=normalizeMercs(p.activeMercs||[],p);
    if(p.activeMercs.length>=MAX_ACTIVE_MERCS){socket.emit("mercHireDenied",{reason:`Max ${MAX_ACTIVE_MERCS} mercenary ships active.`});return;}
    const cat=generateMercOffersForPlayer(p);
    const offer=cat.offers.find(o=>o.id===String(offerId||""));
    if(!offer){socket.emit("mercHireDenied",{reason:"That mercenary contract expired."});return;}
    if((p.credits||0)<offer.price){socket.emit("mercHireDenied",{reason:`Need ${offer.price}cr.`});return;}
    p.credits-=offer.price;
    const merc={...offer,id:`merc_${p.id}_${Date.now()}_${Math.floor(Math.random()*9999)}`,hp:offer.maxHp,shield:offer.maxShield,x:p.x+Math.random()*40-20,y:p.y+Math.random()*40-20,lastShotAt:0};
    p.activeMercs.push(merc);
    syncAndPersist(p,"hire_merc");
    socket.emit("mercHireConfirm",{merc:publicMerc(merc),credits:p.credits,activeMercs:p.activeMercs.map(publicMerc),maxActive:MAX_ACTIVE_MERCS});
  });

  socket.on("mercDestroyed",({mercId})=>{
    const p=players.get(socket.id);if(!p)return;
    const before=(p.activeMercs||[]).length;p.activeMercs=(p.activeMercs||[]).filter(m=>m.id!==String(mercId||""));
    if(p.activeMercs.length!==before){persistPlayerSoon(p,"merc_destroyed");socket.emit("mercState",{activeMercs:p.activeMercs.map(publicMerc),maxActive:MAX_ACTIVE_MERCS});}
  });

  socket.on("mercAttackPlayer",({targetId,mercId,damage,x,y})=>{
    const owner=players.get(socket.id),target=players.get(String(targetId||""));
    if(!owner||!target||owner.mode!=="space"||target.mode!=="space"||target.hp<=0)return;
    if(owner.id===target.id||areAllied(owner,target))return;
    const merc=(owner.activeMercs||[]).find(m=>m.id===String(mercId||""));if(!merc)return;
    const now=Date.now();if(merc.lastShotAt&&now-merc.lastShotAt<520)return;
    const declaredX=Number(x),declaredY=Number(y);
    if(Math.hypot(owner.x-target.x,owner.y-target.y)>2200)return;
    if(Number.isFinite(declaredX)&&Number.isFinite(declaredY)&&Math.hypot(target.x-declaredX,target.y-declaredY)>560)return;
    merc.lastShotAt=now;
    const raw=Math.max(1,Math.min(70,Number(damage)||merc.damage||10));
    const result=applyShieldHullDamageToPlayer(target,raw,true);
    io.to(target.id).emit("hit",{damage:result.damage,hp:target.hp,shield:target.shield,by:`${owner.name}'s mercenary`});
    if(result.killed){target.deaths=(target.deaths||0)+1;owner.kills=(owner.kills||0)+1;addScore(owner,220,"Mercenary Kill");io.to(target.id).emit("youDied",{killedBy:`${owner.name}'s mercenary`});io.emit("playerKilled",{victimId:target.id,victimName:target.name,killerId:owner.id,killerName:owner.name});broadcastLeaderboard();}
  });

  socket.on("civilizationDefenderAttackPlayer",(raw={})=>{
    let {targetId,zoneId,damage,x,y}=raw||{};
    const owner=players.get(socket.id),target=players.get(String(targetId||""));
    if(!owner||!target||owner.mode!=="space"||target.mode!=="space"||target.hp<=0)return;
    if(owner.id===target.id||areAllied(owner,target))return;
    zoneId=safeZoneId(zoneId);
    const zone=civilizationZones.get(zoneId);
    if(!zone||!playerOwnsCivilizationZone(owner,zone))return;
    // Civ-zone NPC ships only defend while the owner is physically inside that civilization zone,
    // and only while the hostile target is still inside / very near the defended zone.
    if(!playerInsideCivilizationZone(owner,zone,60))return;
    if(!playerInsideCivilizationZone(target,zone,180))return;
    const declaredX=Number(x),declaredY=Number(y);
    if(Number.isFinite(declaredX)&&Number.isFinite(declaredY)){
      if(Math.hypot(declaredX-zone.x,declaredY-zone.y)>(zone.radius||420)+260)return;
      if(Math.hypot(target.x-declaredX,target.y-declaredY)>620)return;
    }
    const now=Date.now(),coolKey=`${owner.id}|${zone.zoneId}|${target.id}`;
    const last=civilizationDefenderShotCooldowns.get(coolKey)||0;
    if(now-last<470)return;
    civilizationDefenderShotCooldowns.set(coolKey,now);
    const safeDamage=Math.max(1,Math.min(38,Number(damage)||12));
    const result=applySpaceDamageToPlayer(target,safeDamage,owner,"Civilization Defenders");
    socket.emit("civilizationDefenderAttackConfirm",{targetId:target.id,zoneId:zone.zoneId,damage:result.damage});
  });

  socket.on("turretAttackPlayer",({targetId,structureKey,damage,x,y})=>{
    const owner=players.get(socket.id),target=players.get(String(targetId||""));
    if(!owner||!target||owner.mode!=="space"||target.mode!=="space"||target.hp<=0)return;
    if(owner.id===target.id||areAllied(owner,target))return;
    const st=ownedStructures.get(String(structureKey||""));
    if(!st||st.ownerId!==owner.id||st.type!=="defense_turret"||st.destroyed)return;
    const now=Date.now();if(st.lastShotAt&&now-st.lastShotAt<520)return;
    const declaredX=Number(x),declaredY=Number(y),range=turretRange(st)+260;
    if(Math.hypot(target.x-st.x,target.y-st.y)>range)return;
    if(Number.isFinite(declaredX)&&Number.isFinite(declaredY)&&Math.hypot(declaredX-st.x,declaredY-st.y)>range)return;
    st.lastShotAt=now;
    const safeDamage=Math.max(1,Math.min(turretDamage(st),Number(damage)||turretDamage(st)));
    const result=applySpaceDamageToPlayer(target,safeDamage,owner,"Defense Turret");
    socket.emit("turretAttackConfirm",{targetId:target.id,structureKey:st.key,damage:result.damage});
  });

  socket.on("requestPlayerStructures",()=>{emitPlayerStructures(socket);});

  socket.on("buyStructure",({type,x,y})=>{
    const p=players.get(socket.id);if(!p)return;
    type=String(type||"");const def=PLAYER_STRUCTURE_TYPES[type];if(!def){socket.emit("structureDenied",{reason:"Unknown structure."});return;}
    x=Math.round(Number(x)||p.x);y=Math.round(Number(y)||p.y);
    if(Math.hypot(p.x-x,p.y-y)>320){socket.emit("structureDenied",{reason:"Build closer to your ship."});return;}
    if((p.credits||0)<def.price){socket.emit("structureDenied",{reason:`Need ${def.price}cr.`});return;}
    const key=`${type}_${Math.round(x/80)}_${Math.round(y/80)}`;
    if(ownedStructures.has(key)||ownedStations.has(`${Math.round(x/100)}_${Math.round(y/100)}`)){socket.emit("structureDenied",{reason:"Location occupied."});return;}
    p.credits-=def.price;
    const st={key,type,ownerId:p.id,ownerMemberId:p.memberId||null,ownerName:p.name,x,y,createdAt:Date.now(),...structureDefaultState(type)};if(type==="defense_turret")st.turretCosmeticKey=p.equippedCosmetics?.turret||null;
    ownedStructures.set(key,st);syncAndPersist(p,"buy_structure");
    socket.emit("structureBuildConfirm",{structure:publicStructure(st,p.id),credits:p.credits});broadcastPlayerStructuresList();
  });

  socket.on("depositStorageItem",({structureKey,resourceType,quantity})=>{
    const p=players.get(socket.id);if(!p)return;const st=ownedStructures.get(String(structureKey||""));
    resourceType=String(resourceType||"");quantity=Math.max(1,Math.min(999,Math.floor(Number(quantity)||1)));
    if(!st||st.ownerId!==p.id||st.type!=="storage_facility"||st.destroyed){socket.emit("storageDenied",{reason:"Storage unavailable."});return;}
    if(!isInventoryItemKey(resourceType)||inventoryCount(p,resourceType)<quantity){socket.emit("storageDenied",{reason:"You do not have that item."});return;}
    if(!canFitStorage(st,resourceType,quantity)){socket.emit("storageDenied",{reason:"Storage slots full."});return;}
    removeInventory(p,resourceType,quantity);addStorage(st,resourceType,quantity);syncAndPersist(p,"storage_deposit");
    socket.emit("storageUpdate",{structure:publicStructure(st,p.id),credits:p.credits,nextStorageUpgradeCost:Number(st.storageSlots||24)<100?structureUpgradeCost(st,"storage"):0});broadcastPlayerStructuresList();
  });

  socket.on("withdrawStorageItem",({structureKey,resourceType,quantity})=>{
    const p=players.get(socket.id);if(!p)return;const st=ownedStructures.get(String(structureKey||""));
    resourceType=String(resourceType||"");quantity=Math.max(1,Math.min(999,Math.floor(Number(quantity)||1)));
    if(!st||st.ownerId!==p.id||st.type!=="storage_facility"||st.destroyed){socket.emit("storageDenied",{reason:"Storage unavailable."});return;}
    if(!isInventoryItemKey(resourceType)||inventoryCount({invSlots:st.invSlots,maxSlots:st.storageSlots},resourceType)<quantity){socket.emit("storageDenied",{reason:"Storage does not have that item."});return;}
    if(!canFitInventory(p,resourceType,quantity)){socket.emit("storageDenied",{reason:"Inventory slots full."});return;}
    removeStorage(st,resourceType,quantity);addInventory(p,resourceType,quantity);syncAndPersist(p,"storage_withdraw");
    socket.emit("storageUpdate",{structure:publicStructure(st,p.id),credits:p.credits,nextStorageUpgradeCost:Number(st.storageSlots||24)<100?structureUpgradeCost(st,"storage"):0});broadcastPlayerStructuresList();
  });

  socket.on("upgradeStorageSlots",({structureKey})=>{
    const p=players.get(socket.id);if(!p)return;const st=ownedStructures.get(String(structureKey||""));
    if(!st||st.ownerId!==p.id||st.type!=="storage_facility"||st.destroyed){socket.emit("storageDenied",{reason:"Storage unavailable."});return;}
    if((st.storageSlots||24)>=100){socket.emit("storageDenied",{reason:"Storage is already maxed."});return;}
    const cost=structureUpgradeCost(st,"storage");if((p.credits||0)<cost){socket.emit("storageDenied",{reason:`Need ${cost}cr.`});return;}
    p.credits-=cost;const old=st.storageSlots||24;st.storageSlots=Math.min(100,old+4);st.invSlots=normalizeStorageSlots(st.invSlots,st.storageSlots);
    syncAndPersist(p,"storage_upgrade");socket.emit("storageUpdate",{structure:publicStructure(st,p.id),credits:p.credits,cost,nextStorageUpgradeCost:Number(st.storageSlots||24)<100?structureUpgradeCost(st,"storage"):0});broadcastPlayerStructuresList();
  });

  socket.on("upgradeStorageShield",({structureKey})=>{
    const p=players.get(socket.id),st=ownedStructures.get(String(structureKey||""));
    if(!p||!st||st.ownerId!==p.id||st.type!=="storage_facility"||st.destroyed){socket.emit("storageDenied",{reason:"Storage unavailable."});return;}
    const cost=structureUpgradeCost(st,"storageShield");if((p.credits||0)<cost){socket.emit("storageDenied",{reason:`Need ${cost.toLocaleString()}cr.`});return;}
    p.credits-=cost;st.storageShieldLevel=Math.max(1,(st.storageShieldLevel||1)+1);st.maxShield=Math.floor((PLAYER_STRUCTURE_TYPES.storage_facility.maxShield||650)*Math.pow(1.18,st.storageShieldLevel-1));st.shield=st.maxShield;
    syncAndPersist(p,"storage_shield_upgrade");socket.emit("storageUpdate",{structure:publicStructure(st,p.id),credits:p.credits,cost,shieldUpgrade:true});broadcastPlayerStructuresList();
  });

  socket.on("upgradeTurret",({structureKey,kind})=>{
    const p=players.get(socket.id);if(!p)return;const st=ownedStructures.get(String(structureKey||""));kind=kind==="shield"?"shield":"damage";
    if(!st||st.ownerId!==p.id||st.type!=="defense_turret"||st.destroyed)return;
    const cost=structureUpgradeCost(st,kind);if((p.credits||0)<cost){socket.emit("structureDenied",{reason:`Need ${cost}cr.`});return;}
    p.credits-=cost;
    if(kind==="damage")st.damageLevel=Math.min(12,(st.damageLevel||1)+1);
    else{st.shieldLevel=Math.min(12,(st.shieldLevel||1)+1);st.maxShield=Math.floor((PLAYER_STRUCTURE_TYPES.defense_turret.maxShield||900)*(1+0.32*((st.shieldLevel||1)-1)));st.shield=st.maxShield;}
    syncAndPersist(p,"turret_upgrade");socket.emit("structureUpdate",{structure:publicStructure(st,p.id),credits:p.credits});broadcastPlayerStructuresList();
  });

  socket.on("environmentalDamagePlayerStructure",({structureKey,damage,source,x,y})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="space")return;const st=ownedStructures.get(String(structureKey||""));if(!st||st.destroyed)return;
    if(Math.hypot(p.x-st.x,p.y-st.y)>2800)return;
    const declaredX=Number(x),declaredY=Number(y);if(Number.isFinite(declaredX)&&Number.isFinite(declaredY)&&Math.hypot(declaredX-st.x,declaredY-st.y)>1600)return;
    const result=applyStructureDamage(st,damage);io.emit("playerStructureDamaged",{structureKey:st.key,hp:st.hp,maxHp:st.maxHp,shield:st.shield,maxShield:st.maxShield,ownerName:st.ownerName,attackerName:String(source||"Raider").slice(0,32)});
    if(result.destroyed){st.destroyed=true;io.emit("playerStructureDestroyed",{structureKey:st.key,x:st.x,y:st.y,type:st.type,ownerName:st.ownerName});}
    broadcastPlayerStructuresList();const owner=players.get(st.ownerId);if(owner)persistPlayerSoon(owner,"structure_damage");
  });

  socket.on("collectOwnedStation",({stationKey})=>{
    const p=players.get(socket.id);if(!p)return;
    const st=ownedStations.get(stationKey);if(!st||st.ownerId!==p.id||st.destroyed)return;
    const goods={...st.accumulatedGoods};
    for(const [k,v] of Object.entries(goods))if(v>0)addInventory(p,k,v);
    socket.emit("ownedStationGoods",{stationKey,goods,serverAuthoritative:true});
    st.accumulatedGoods={};syncAndPersist(p,"collect_station_goods");
  });

  socket.on("npcHitPlayer",({damage,source})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="space"||p.hp<=0)return;
    const raw=Math.max(0,Math.min(90,Number(damage)||0));if(raw<=0)return;
    const result=applyShieldHullDamageToPlayer(p,raw,true);
    socket.emit("hit",{damage:result.damage,hp:p.hp,shield:p.shield,by:source||"Trade Ship"});
    if(result.killed){
      p.deaths=(p.deaths||0)+1;
      socket.emit("youDied",{killedBy:source||"Trade Ship"});
      io.emit("playerKilled",{victimId:p.id,victimName:p.name,killerId:null,killerName:source||"Trade Ship"});
      broadcastLeaderboard();
      setTimeout(()=>{
        const rp=players.get(socket.id);if(!rp)return;
        const sp=computeSpawnPoint();rp.x=sp.x;rp.y=sp.y;rp.hp=rp.maxHp;rp.shield=rp.maxShield;rp.energy=100;rp.shieldRegenTimer=0;
        socket.emit("respawn",{x:rp.x,y:rp.y});
      },3000);
    }
  });

  socket.on("destroyOwnedTradeShip",({stationKey,shipId})=>{
    const p=players.get(socket.id);if(!p)return;
    const st=ownedStations.get(stationKey);if(!st||!shipId)return;
    const idx=st.hiredShips.findIndex(sh=>sh.id===shipId);
    if(idx<0)return;
    const sh=st.hiredShips[idx];
    addScore(p,75,"Trade Ship Destroyed");
    if(st.destroyed){
      st.hiredShips.splice(idx,1);
    }else{
      const delay=stationDefenseStats(st.tier).respawnDelay;
      sh.state="respawning";sh.respawnAt=Date.now()+delay;sh.cargo={};
    }
    socket.emit("ownedTradeShipDestroyConfirm",{stationKey,shipId});
    const owner=players.get(st.ownerId);if(owner)persistPlayerSoon(owner,"station_ship_destroyed");
    broadcastOwnedStationsList();
  });

  socket.on("damageOwnedStation",({stationKey,damage})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="space")return;
    const st=ownedStations.get(stationKey);if(!st||st.destroyed)return;
    if(st.ownerId===p.id){socket.emit("stationDamageDenied",{stationKey,reason:"You cannot attack your own station."});return;}
    const owner=players.get(st.ownerId);if(owner&&areAllied(p,owner)){socket.emit("stationDamageDenied",{stationKey,reason:"Friendly faction/party station."});return;}
    if(Math.hypot(p.x-st.x,p.y-st.y)>1200)return;
    const result=applyStationDamage(st,damage);
    for(const sh of st.hiredShips){
      if(sh.state==="respawning")sh.respawnAt=Math.min(sh.respawnAt||Infinity,Date.now()+5000);
      else sh.state="defending";
    }
    socket.emit("ownedStationHitConfirm",{stationKey,hp:st.hp,maxHp:st.maxHp,shield:st.shield,maxShield:st.maxShield,damage:result.damage});
    io.emit("ownedStationDamaged",{stationKey,hp:st.hp,maxHp:st.maxHp,shield:st.shield,maxShield:st.maxShield,ownerName:st.ownerName,attackerName:p.name});
    if(result.destroyed)destroyOwnedStation(st,p);
    broadcastOwnedStationsList();
  });

  socket.on("environmentalDamageOwnedStation",({stationKey,damage,source,x,y})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="space")return;
    stationKey=String(stationKey||"");
    const st=ownedStations.get(stationKey);if(!st||st.destroyed)return;
    // This is used for client-side PvE hazards like pirate raiders.
    // Keep it capped, proximity-checked, and rate-limited so it cannot become a free high-damage grief tool.
    if(Math.hypot(p.x-st.x,p.y-st.y)>2600)return;
    const declaredX=Number(x),declaredY=Number(y);
    if(Number.isFinite(declaredX)&&Number.isFinite(declaredY)&&Math.hypot(declaredX-st.x,declaredY-st.y)>1800)return;
    const now=Date.now(),coolKey=`${socket.id}|${stationKey}|${String(source||"hazard").slice(0,24)}`;
    const last=stationHazardDamageCooldowns.get(coolKey)||0;
    if(now-last<520)return;
    stationHazardDamageCooldowns.set(coolKey,now);
    const safeDamage=Math.max(1,Math.min(45,Number(damage)||8));
    const result=applyStationDamage(st,safeDamage);
    for(const sh of st.hiredShips){
      if(sh.state==="respawning")sh.respawnAt=Math.min(sh.respawnAt||Infinity,Date.now()+5000);
      else sh.state="defending";
    }
    io.emit("ownedStationDamaged",{stationKey,hp:st.hp,maxHp:st.maxHp,shield:st.shield,maxShield:st.maxShield,ownerName:st.ownerName,attackerName:String(source||"Pirate Raiders").slice(0,32)});
    socket.emit("ownedStationHitConfirm",{stationKey,hp:st.hp,maxHp:st.maxHp,shield:st.shield,maxShield:st.maxShield,damage:result.damage});
    if(result.destroyed)destroyOwnedStation(st,null);
    broadcastOwnedStationsList();
  });

  socket.on("useOxygenTank",()=>{
    const p=players.get(socket.id);if(!p)return;
    if(!removeInventory(p,"oxygen_tank",1)){socket.emit("useItemDenied",{type:"oxygen_tank",reason:"No oxygen tank in server inventory."});return;}
    socket.emit("oxygenTankUsed",{credits:p.credits,maxSlots:p.maxSlots,invSlots:p.invSlots});syncAndPersist(p,"use_oxygen_tank");
  });

  socket.on("useGas",()=>{
    const p=players.get(socket.id);if(!p)return;
    if(!removeInventory(p,"gas_canister",1)){socket.emit("useItemDenied",{type:"gas_canister",reason:"No gas canister in server inventory."});return;}
    p.energy=Math.min(100,p.energy+GAS_REFUEL);socket.emit("energyUpdate",{energy:p.energy});syncAndPersist(p,"use_gas");
  });

  socket.on("upgradeAttr",({attr})=>{
    const p=players.get(socket.id);if(!p)return;
    const valid=["damage","speed","braking","armor","gasEfficiency","shieldRegen"];
    if(!valid.includes(attr))return;
    if((p.attrPoints||0)<=0){socket.emit("upgradeDenied",{reason:"No attribute points. Use paid upgrade instead."});return;}
    if((p.attrs[attr]||1)>=10){socket.emit("upgradeDenied",{reason:"Already maxed."});return;}
    p.attrs[attr]=(p.attrs[attr]||1)+1;p.attrPoints=(p.attrPoints||0)-1;
    socket.emit("attrConfirm",{attr,val:p.attrs[attr],attrPoints:p.attrPoints,credits:p.credits,xp:p.xp,level:p.level});syncAndPersist(p,"upgrade_attr");
  });

  socket.on("upgradeAttrPaid",({attr})=>{
    const p=players.get(socket.id);if(!p)return;
    const valid=["damage","speed","braking","armor","gasEfficiency","shieldRegen"];
    attr=String(attr||"");
    if(!valid.includes(attr))return;
    if((p.attrs[attr]||1)>=10){socket.emit("upgradeDenied",{reason:"Already maxed."});return;}
    const cost=attrUpgradeCost(p,attr);
    if((p.credits||0)<cost.credits){socket.emit("upgradeDenied",{reason:`Need ${cost.credits}cr.`});return;}
    if((p.xp||0)<cost.xp){socket.emit("upgradeDenied",{reason:`Need ${cost.xp}XP saved.`});return;}
    p.credits-=cost.credits;
    p.xp-=cost.xp;
    p.attrs[attr]=(p.attrs[attr]||1)+1;
    socket.emit("attrConfirm",{attr,val:p.attrs[attr],attrPoints:p.attrPoints||0,credits:p.credits,xp:p.xp,level:p.level,cost});
    syncAndPersist(p,"upgrade_attr_paid");
  });

  socket.on("gainXp",({amount})=>{
    const p=players.get(socket.id);if(!p||amount<=0||amount>500)return;
    grantXp(p,Math.floor(Number(amount)||0),"Mining/Combat");
  });

  socket.on("chat",({message})=>{
    const p=players.get(socket.id);if(!p)return;
    broadcastChat(p.name,message,p.color);
  });

  socket.on("clientPing",(payload={},ack)=>{
    if(typeof payload==="function"){ack=payload;payload={};}
    const p=players.get(socket.id);if(!p)return;
    const now=Date.now();if(p.pingTs)p.ping=Math.min(999,now-p.pingTs);p.pingTs=now;
    const pong={ok:true,serverNow:now,echo:Math.max(0,Math.floor(Number(payload?.seq)||0))};
    socket.emit("serverPong",pong);
    if(typeof ack==="function")ack(pong);
  });

  socket.on("requestLeaderboard",()=>socket.emit("leaderboard",buildLeaderboard(10)));
  socket.on("requestServerList",()=>socket.emit("serverList",{name:SERVER_NAME,players:[...players.values()].map(serverListSnap),uptime:Math.floor((Date.now()-SERVER_START)/1000)}));
  socket.on("requestOwnedStations",()=>emitOwnedStationsList(socket));

  socket.on("disconnect",()=>{
    const p=players.get(socket.id);
    if(p)rememberAccountLivePosition(p,"disconnect");
    const keepForReconnect=!!(p&&rememberTransientReconnectSession(p,p.connectionResumeToken));
    if(p){broadcastChat("Server",`${p.name} has left the galaxy.`,"#ff8888");socket.broadcast.emit("playerLeft",{id:socket.id});if(p.memberId){if(isCurrentAccountSocket(p)){persistPlayerNow(p,"disconnect");socketsByMemberId.delete(String(p.memberId));}else{cancelPersistTimerForPlayerId(p.id);}}else persistPlayerNow(p,"disconnect");}
    for(const ts of [...tradeSessions.values()])if(ts.a===socket.id||ts.b===socket.id)cancelTrade(ts,"Trade cancelled: player disconnected.");
    if(p?.partyId&&!keepForReconnect)leaveParty(socket.id,"Disconnected from party.");
    if(p?.factionId){const f=factions.get(p.factionId);if(f)emitFactionState(f.id);}
    players.delete(socket.id);broadcastLeaderboard();broadcastServerList();
  });
});

const PORT = Number(process.env.PORT) || 3000;
const HOST = process.env.HOST || "0.0.0.0";
server.listen(PORT, HOST, () => {
  console.log(`🚀 ${SERVER_NAME} listening on ${HOST}:${PORT} | ${TICK_RATE}Hz | Max:${MAX_PLAYERS}`);
  console.log("🌍 Global lobby ready. Point every client at your Railway public URL, not localhost.");
});
