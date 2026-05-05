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
  pingTimeout: 20000, pingInterval: 10000
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
const WIX_PERSIST_SECRET = process.env.WIX_PERSIST_SECRET || process.env.SPACE_ECO_PERSIST_SECRET || PURCHASE_WEBHOOK_SECRET || "";
const socketsByMemberId = new Map();
const persistTimers = new Map();
console.log("Space Eco persistence config", {
  hasGameAuthSecret: !!WIX_GAME_AUTH_SECRET,
  hasPersistUrl: !!WIX_PERSIST_URL,
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
  miner_mantis:{ name:"Miner Mantis",price:0,craftOnly:true,description:"Crafted mining cutter with an ore scanner and reinforced storage racks.",maxHp:145,maxShield:75,thrustMult:1.05,cargoMult:2.7,damageMult:1.05,shieldRegenMult:1.0,size:"large",specialty:"Mining",recipe:{credits:6000,hull_plate:4,engine_core:2,cargo_pod:4,copper:40,iron:30}},
  guardian:    { name:"Guardian",price:0,craftOnly:true,description:"Crafted escort cruiser built to protect stations and allies.",maxHp:230,maxShield:210,thrustMult:0.82,cargoMult:1.2,damageMult:1.65,shieldRegenMult:1.8,size:"large",specialty:"Defense escort",recipe:{credits:11000,hull_plate:8,shield_matrix:3,weapon_array:2,iron:70,gold:20}},
  solar_sprinter:{ name:"Solar Sprinter",price:0,craftOnly:true,description:"Crafted solar racer with excellent fuel efficiency and long-range scout speed.",maxHp:95,maxShield:95,thrustMult:1.85,cargoMult:0.85,damageMult:1.25,shieldRegenMult:1.45,size:"small",specialty:"Speed + fuel",recipe:{credits:14000,engine_core:5,nav_chip:3,crystal:25,fuel:20}},
  obelisk_carrier:{ name:"Obelisk Carrier",price:0,craftOnly:true,description:"Crafted mothership-class carrier with heavy shields and command presence.",maxHp:390,maxShield:260,thrustMult:0.50,cargoMult:3.4,damageMult:2.35,shieldRegenMult:0.95,size:"huge",specialty:"Mothership",recipe:{credits:45000,obelisk_core:1,hull_plate:16,shield_matrix:8,weapon_array:6,cargo_pod:10,crystal:70,gold:100,magma_core:40}},
};

/* ── Owned station tiers ── */
const OWNED_STATION_TIERS = {
  outpost:  { name:"Personal Outpost",  price:5000,  maxShips:3,  shipHireCost:500,  collectRange:800  },
  base:     { name:"Trade Base",        price:15000, maxShips:6,  shipHireCost:1200, collectRange:1400 },
  fortress: { name:"War Fortress",      price:40000, maxShips:10, shipHireCost:2500, collectRange:2200 },
};

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

/* ── Player state ── */
const players = new Map();

function defaultPlayer(id, name, x, y) {
  return {
    id, name:sanitizeName(name), x, y,
    vx:0, vy:0, angle:0,
    hp:100, maxHp:100, shield:60, maxShield:60,
    level:1, xp:0, attrPoints:0,
    credits:300, color:randomShipColor(), shipType:"scout",
    input:{ rotLeft:false, rotRight:false, thrust:false, brake:false, shootX:null, shootY:null },
    shootCooldown:0, lastSeen:Date.now(), mode:"space", planetId:null,
    attrs:{ damage:1, speed:1, cargoMax:1, armor:1, gasEfficiency:1, shieldRegen:1 },
    energy:100, shieldRegenTimer:0,
    score:0, kills:0, deaths:0, tradingVolume:0, miningScore:0,
    ping:0, pingTs:0,
    planetX:0, planetY:0, planetVx:0, planetVy:0, planetTool:"mining",
    cosmeticColor:"#ffd27a", suitColor:"#ffffff", weaponLevel:1, miningLevel:1, oxygenLevel:1,
    badgeRewards:{},
  };
}

function sanitizeName(raw) { return String(raw||"Pilot").replace(/[^a-zA-Z0-9_ \-]/g,"").slice(0,16).trim()||"Pilot"; }
function randomShipColor() { const p=["#7be6ff","#ff9944","#66ff88","#ff66aa","#ffdd44","#cc88ff","#44ccff","#ff6644"]; return p[Math.floor(Math.random()*p.length)]; }

function characterUpgradeCost(player,kind){
  const levels={weapon:player.weaponLevel||1,mining:player.miningLevel||1,oxygen:player.oxygenLevel||1};
  const base={weapon:750,mining:650,oxygen:500}[kind]||999999;
  return Math.floor(base*Math.pow(1.65,Math.max(0,(levels[kind]||1)-1)));
}
function planetWeaponDamage(player){return 12+((player.weaponLevel||1)-1)*5;}
function sendCharacterState(socket,p){socket.emit("characterState",{cosmeticColor:p.cosmeticColor,suitColor:p.suitColor,weaponLevel:p.weaponLevel||1,miningLevel:p.miningLevel||1,oxygenLevel:p.oxygenLevel||1,credits:p.credits});}

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

const RES_KEYS=["dirt","stone","copper","iron","gold","crystal","fuel","gas_canister","oxygen_tank","ice_block","lava_rock","magma_core","toxic_sludge","sand","grass_tuft","hull_plate","engine_core","shield_matrix","weapon_array","cargo_pod","nav_chip","obelisk_core"];
const RES_BASE={dirt:1,stone:3,copper:9,iron:10,gold:40,crystal:60,fuel:25,gas_canister:30,oxygen_tank:35,ice_block:4,lava_rock:12,magma_core:22,toxic_sludge:8,sand:2,grass_tuft:1,hull_plate:85,engine_core:140,shield_matrix:170,weapon_array:190,cargo_pod:95,nav_chip:155,obelisk_core:800};
const RES_RARITY={dirt:1,stone:2,copper:3,iron:3,gold:5,crystal:6,fuel:4,gas_canister:2,oxygen_tank:2,ice_block:2,lava_rock:3,magma_core:4,toxic_sludge:3,sand:1,grass_tuft:1,hull_plate:5,engine_core:6,shield_matrix:6,weapon_array:6,cargo_pod:5,nav_chip:6,obelisk_core:8};
const econRng=makeRng(GALAXY_SEED+"|economy");
const economy={
  drift:Object.fromEntries(RES_KEYS.map(k=>[k,1])),
  scarcity:Object.fromEntries(RES_KEYS.map(k=>[k,1])),
  tick(){for(const k of RES_KEYS){this.drift[k]=Math.max(0.6,Math.min(1.6,this.drift[k]+(econRng()-0.5)*0.02));this.scarcity[k]+=(1-this.scarcity[k])*0.002;}},
  price(k){const b=RES_BASE[k]||1,r=RES_RARITY[k]||1,f=1+(r-1)*0.28;return Math.max(1,Math.round(b*f*this.drift[k]*this.scarcity[k]));},
  sold(k,q){this.scarcity[k]=Math.max(0.5,Math.min(1.5,this.scarcity[k]-q*0.02));},
  bought(k,q){this.scarcity[k]=Math.max(0.5,Math.min(1.5,this.scarcity[k]+q*0.02));},
  snapshot(){const o={};for(const k of RES_KEYS)o[k]=this.price(k);return o;}
};

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
      if(type&&RES_KEYS.includes(type)&&count>0)out[i]={type,count};
    }
  }else if(slots&&typeof slots==="object"){
    let idx=0;
    for(const [type,val] of Object.entries(slots)){
      let count=Math.max(0,Math.min(9999,Math.floor(Number(val)||0)));
      if(!RES_KEYS.includes(type)||count<=0)continue;
      while(count>0&&idx<maxSlots){const put=Math.min(24,count);out[idx++]={type,count:put};count-=put;}
    }
  }
  return out;
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
  if(!RES_KEYS.includes(type))return false;
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
  for(const it of Array.isArray(items)?items:[]){const type=String(it.type||"");const qty=Math.max(1,Math.min(48,Math.floor(Number(it.qty)||0)));if(RES_KEYS.includes(type))normalized.push({type,qty});}
  for(const it of normalized){if(!canFitInventory(p,it.type,it.qty))return {ok:false,reason:"Inventory full for reward items."};}
  if(credits>0)p.credits=(p.credits||0)+credits;
  for(const it of normalized)addInventory(p,it.type,it.qty);
  if(xp>0)grantXp(p,xp,reason);
  return {ok:true,credits,xp,items:normalized};
}
function validateTradeItems(p,items){
  const need={};for(const it of items||[]){const type=String(it.type||"");const q=Math.max(0,Math.floor(Number(it.quantity)||0));if(!RES_KEYS.includes(type)||q<=0)return false;need[type]=(need[type]||0)+q;}
  return Object.entries(need).every(([type,q])=>inventoryCount(p,type)>=q);
}
function emitInventorySync(p,reason="sync"){
  if(!p?.id)return;
  io.to(p.id).emit("inventorySync",{credits:p.credits||0,maxSlots:p.maxSlots||24,invSlots:p.invSlots||emptySlots(24),inventory:inventoryCounts(p),reason});
}
async function persistPlayerNow(p,reason="update"){
  if(!p?.memberId){console.warn("Wix persistence skipped: player has no memberId", p?.id, reason);return;}
  if(!WIX_PERSIST_URL||!WIX_PERSIST_SECRET){console.warn("Wix persistence skipped: missing WIX_PERSIST_URL or WIX_PERSIST_SECRET", {hasUrl:!!WIX_PERSIST_URL,hasSecret:!!WIX_PERSIST_SECRET});return;}
  const payload={memberId:p.memberId,displayName:p.name,credits:p.credits||0,maxSlots:p.maxSlots||24,invSlots:p.invSlots||emptySlots(24),level:p.level||1,xp:p.xp||0,shipType:p.shipType||"scout",attrs:p.attrs||{},badgeRewards:p.badgeRewards||{},reason,updatedAt:Date.now()};
  try{
    const res = await fetch(WIX_PERSIST_URL,{method:"POST",headers:{"Content-Type":"application/json","Authorization":`Bearer ${WIX_PERSIST_SECRET}`},body:JSON.stringify(payload)});
    if(!res.ok){
      const text = await res.text().catch(()=>"");
      console.warn("Wix persistence failed response:", res.status, text.slice(0,300));
    }
  }catch(err){console.warn("Wix persistence failed:",err?.message||err);}
}
function persistPlayerSoon(p,reason="update",delay=1200){
  if(!p?.memberId)return;
  if(persistTimers.has(p.id))clearTimeout(persistTimers.get(p.id));
  persistTimers.set(p.id,setTimeout(()=>{persistTimers.delete(p.id);persistPlayerNow(p,reason);},delay));
}
function syncAndPersist(p,reason="sync"){
  emitInventorySync(p,reason);persistPlayerSoon(p,reason);
}
function applyAuthAccountToPlayer(p,auth){
  if(!auth)return;
  p.memberId=String(auth.memberId);p.accountLoaded=true;
  p.name=sanitizeName(auth.displayName||p.name||"Pilot");
  p.credits=Math.max(0,Math.floor(Number(auth.credits)||p.credits||300));
  p.maxSlots=Math.max(24,Math.min(96,Math.floor(Number(auth.maxSlots)||24)));
  p.invSlots=normalizeInventorySlots(auth.invSlots||auth.inventory,p.maxSlots);
  if(auth.shipType&&SHIP_TYPES[auth.shipType])p.shipType=auth.shipType;
  if(auth.level)p.level=Math.max(1,Math.floor(Number(auth.level)||1));
  if(auth.xp!==undefined)p.xp=Math.max(0,Math.floor(Number(auth.xp)||0));
  if(auth.attrs&&typeof auth.attrs==="object")p.attrs={...p.attrs,...auth.attrs};
  if(auth.badgeRewards&&typeof auth.badgeRewards==="object")p.badgeRewards={...auth.badgeRewards};
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
  const type=["lush","desert","ice","toxic","volcanic"].includes(raw.type)?raw.type:"lush";
  const id=String(raw.id||`${type}_${Math.round(raw.x||0)}_${Math.round(raw.y||0)}`).slice(0,120);
  const seed=String(raw.seed||`${GALAXY_SEED}|planet|${id}`).slice(0,180);
  const resList=Array.isArray(raw.resList)?raw.resList.filter(k=>RES_KEYS.includes(k)).slice(0,10):["dirt","stone","copper","iron"];
  return {id,seed,type,resList,x:Number(raw.x)||0,y:Number(raw.y)||0,radius:Number(raw.radius)||40};
}
function genPlanetMapServer(planet){
  const rng=makeRng(planet.seed+"|map"),W=320,H=140,sy2=45+Math.floor(rng()*13)-6;
  const heights=new Array(W).fill(0).map((_,x)=>Math.floor(sy2+Math.sin((x/28)+rng()*10)*6+Math.sin((x/9)+rng()*10)*2+(rng()-0.5)*2));
  const tiles=new Uint8Array(W*H),hp=new Uint8Array(W*H),idx=(x,y)=>y*W+x;
  const tc={lush:{surface:13,shallow:1,deep:2,sHP:20,shHP:25,dHP:55},desert:{surface:11,shallow:11,deep:12,sHP:18,shHP:22,dHP:50},ice:{surface:6,shallow:6,deep:7,sHP:30,shHP:35,dHP:65},toxic:{surface:10,shallow:1,deep:2,sHP:22,shHP:28,dHP:60},volcanic:{surface:9,shallow:8,deep:2,sHP:40,shHP:50,dHP:70}};
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
function planetResForTile(planet,t,y,H){
  const d=y/H,l=planet.resList&&planet.resList.length?planet.resList:["dirt","stone","copper","iron"];
  if(t===1)return"dirt";if(t===13)return Math.random()<0.3?"grass_tuft":"dirt";if(t===11)return"sand";if(t===6)return"ice_block";if(t===7)return Math.random()<0.6?"ice_block":"stone";if(t===8)return"lava_rock";if(t===9)return Math.random()<0.7?"magma_core":"lava_rock";if(t===10)return"toxic_sludge";if(t===2||t===12)return"stone";if(t===3){const m=l.filter(k=>["copper","iron"].includes(k));return m.length?m[Math.floor(Math.random()*m.length)]:"copper";}if(t===4){if(l.includes("gold")&&Math.random()<0.55)return"gold";if(l.includes("crystal")&&Math.random()<0.65)return"crystal";return l[Math.floor(Math.random()*l.length)];}if(t===5){if(l.includes("crystal")&&Math.random()<0.6+d*0.3)return"crystal";if(l.includes("gold")&&Math.random()<0.4+d*0.3)return"gold";return l[l.length-1];}return"stone";
}
function hpForPlacedTile(tile){return ({1:22,2:55,6:30,8:45,10:28,11:18,13:20})[tile]||25;}


/* ── Credit purchase API called by Wix backend only ── */
app.get("/api/credit-packages", (_req,res)=>{
  res.json(Object.fromEntries(Object.entries(CREDIT_PACKAGES).map(([id,p])=>[id,{credits:p.credits,amount:p.amount,label:p.label}])));
});
app.post("/api/grant-credits", (req,res)=>{
  if(!PURCHASE_WEBHOOK_SECRET){res.status(500).json({ok:false,error:"PURCHASE_WEBHOOK_SECRET is not configured on Railway."});return;}
  const auth=req.get("authorization")||"";
  if(auth!==`Bearer ${PURCHASE_WEBHOOK_SECRET}`){res.status(401).json({ok:false,error:"Unauthorized."});return;}
  const {paymentId,packageId,socketId}=req.body||{};
  if(!paymentId||!packageId||!socketId){res.status(400).json({ok:false,error:"paymentId, packageId, and socketId are required."});return;}
  const pack=CREDIT_PACKAGES[packageId];
  if(!pack){res.status(400).json({ok:false,error:"Unknown credit package."});return;}
  if(grantedCreditPayments.has(paymentId)){res.json({ok:true,duplicate:true,grant:grantedCreditPayments.get(paymentId)});return;}
  const p=players.get(socketId);
  if(!p){res.status(409).json({ok:false,error:"Player socket is not online. Add account persistence before granting offline purchases."});return;}
  p.credits+=pack.credits;
  const grant={paymentId,packageId,socketId,playerName:p.name,memberId:p.memberId||null,creditsAdded:pack.credits,credits:p.credits,grantedAt:Date.now()};
  grantedCreditPayments.set(paymentId,grant);
  addScore(p,Math.floor(pack.credits*0.002),"Credit Purchase");
  io.to(socketId).emit("creditPurchaseConfirm",grant);
  io.to(socketId).emit("creditUpdate",{credits:p.credits});
  syncAndPersist(p,"credit_purchase");
  res.json({ok:true,grant});
});

/* ── PvP projectiles ── */
const pvpProjectiles=[];
const planetProjectiles=[];
const SHOOT_CD=0.22, PROJ_SPEED=280, PROJ_LIFE=2.2, BASE_DAMAGE=18;
const PLANET_PROJ_SPEED=245, PLANET_PROJ_LIFE=1.7, PLANET_PROJ_HIT_RADIUS=11;

function tickProjectiles(dt){
  for(let i=pvpProjectiles.length-1;i>=0;i--){
    const p=pvpProjectiles[i];p.x+=p.vx*dt;p.y+=p.vy*dt;p.life-=dt;
    if(p.life<=0){pvpProjectiles.splice(i,1);continue;}
    for(const[sid,target]of players){
      if(sid===p.ownerId||target.mode!=="space")continue;
      if(areAllied(players.get(p.ownerId),target))continue;
      if(Math.hypot(p.x-target.x,p.y-target.y)<12){
        const armor=1+((target.attrs.armor-1)*0.2);let dmg=p.damage/armor;
        if(target.shield>0){const abs=Math.min(target.shield,dmg);target.shield-=abs;dmg-=abs;}
        target.hp=Math.max(0,target.hp-dmg);target.shieldRegenTimer=4;
        io.to(sid).emit("hit",{damage:Math.round(dmg),hp:target.hp,shield:target.shield,by:p.ownerId});
        io.to(p.ownerId).emit("hitConfirm",{targetId:sid,damage:Math.round(dmg)});
        pvpProjectiles.splice(i,1);
        if(target.hp<=0)handlePlayerKill(sid,p.ownerId);
        break;
      }
    }
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
    const sp=computeSpawnPoint();rp.mode="space";rp.planetId=null;rp.x=sp.x;rp.y=sp.y;rp.hp=rp.maxHp;rp.shield=rp.maxShield;rp.energy=100;rp.planetX=0;rp.planetY=0;
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
        const armor=1+((target.attrs.armor-1)*0.08),dmg=pr.damage/armor;
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
  setTimeout(()=>{
    const p=players.get(victimId);if(!p)return;
    const sp=computeSpawnPoint();p.x=sp.x;p.y=sp.y;p.hp=p.maxHp;p.shield=p.maxShield;p.energy=100;p.shieldRegenTimer=0;
    io.to(victimId).emit("respawn",{x:p.x,y:p.y});
  },3000);
}

function applySpaceDamageToPlayer(target, rawDamage, attacker, sourceName="Ally Trade Ship"){
  if(!target||target.mode!=="space"||target.hp<=0)return {damage:0,killed:false};
  const amount=Math.max(0,Math.min(220,Number(rawDamage)||0));
  if(amount<=0)return {damage:0,killed:false};
  const armor=1+(((target.attrs||{}).armor-1)*0.2);
  let dmg=amount/Math.max(0.2,armor);
  if(target.shield>0){const abs=Math.min(target.shield,dmg);target.shield-=abs;dmg-=abs;}
  target.hp=Math.max(0,target.hp-dmg);target.shieldRegenTimer=4;
  io.to(target.id).emit("hit",{damage:Math.round(dmg),hp:target.hp,shield:target.shield,by:attacker?.id||sourceName,source:sourceName});
  if(attacker?.id)io.to(attacker.id).emit("hitConfirm",{targetId:target.id,damage:Math.round(dmg),source:sourceName});
  const killed=target.hp<=0;
  if(killed)handlePlayerKill(target.id,attacker?.id||null);
  return {damage:Math.round(dmg),killed};
}

/* ── Physics tick ── */
const ROT_SPEED=2.4, BASE_THRUST=115, ENERGY_DRAIN=1.8, ENERGY_IDLE=0.15, GAS_REFUEL=30;

function tickPlayers(dt){
  for(const[,p]of players){
    if(p.mode!=="space")continue;
    const ship=SHIP_TYPES[p.shipType]||SHIP_TYPES.scout;
    const speedStat=(1+((p.attrs.speed-1)*0.3))*ship.thrustMult;
    const gasEff=1/Math.max(0.3,1+((p.attrs.gasEfficiency-1)*0.15));
    const shRegen=3*(1+((p.attrs.shieldRegen-1)*0.4))*ship.shieldRegenMult;
    const inp=p.input;
    if(inp.rotLeft)p.angle-=ROT_SPEED*dt;
    if(inp.rotRight)p.angle+=ROT_SPEED*dt;
    if(inp.thrust){p.vx+=Math.cos(p.angle)*BASE_THRUST*speedStat*dt;p.vy+=Math.sin(p.angle)*BASE_THRUST*speedStat*dt;p.energy=Math.max(0,p.energy-ENERGY_DRAIN*gasEff*dt);}
    else if(Math.hypot(p.vx,p.vy)>5)p.energy=Math.max(0,p.energy-ENERGY_IDLE*gasEff*dt);
    if(inp.brake){p.vx*=0.92;p.vy*=0.92;}
    const drag=Math.pow(0.995,dt*60);p.vx*=drag;p.vy*=drag;p.x+=p.vx*dt;p.y+=p.vy*dt;
    p.shieldRegenTimer=Math.max(0,p.shieldRegenTimer-dt);
    if(p.shieldRegenTimer<=0&&p.shield<p.maxShield)p.shield=Math.min(p.maxShield,p.shield+shRegen*dt);
    if(inp.shootX!==null&&p.shootCooldown<=0&&p.hp>0){
      const ang=Math.atan2(inp.shootY-p.y,inp.shootX-p.x);
      const dmgStat=(1+((p.attrs.damage-1)*0.4))*ship.damageMult;
      pvpProjectiles.push({id:`${p.id}_${Date.now()}_${Math.random()}`,ownerId:p.id,ownerName:p.name,x:p.x,y:p.y,vx:Math.cos(ang)*PROJ_SPEED,vy:Math.sin(ang)*PROJ_SPEED,damage:BASE_DAMAGE*dmgStat,life:PROJ_LIFE});
      p.shootCooldown=SHOOT_CD;inp.shootX=null;inp.shootY=null;
    }
    if(p.shootCooldown>0)p.shootCooldown=Math.max(0,p.shootCooldown-dt);
    p.lastSeen=Date.now();
  }
}

/* ── Broadcast ── */
function snap(p){return{id:p.id,name:p.name,x:p.x,y:p.y,vx:p.vx,vy:p.vy,angle:p.angle,hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield,shieldRegenTimer:p.shieldRegenTimer||0,color:p.color,level:p.level,mode:p.mode,score:p.score||0,kills:p.kills||0,shipType:p.shipType||"scout",ping:p.ping||0,planetId:p.planetId,planetX:p.planetX||0,planetY:p.planetY||0,cosmeticColor:p.cosmeticColor,suitColor:p.suitColor,weaponLevel:p.weaponLevel||1};}
function serverListSnap(p){return{id:p.id,name:p.name,x:Math.round(p.x),y:Math.round(p.y),level:p.level,score:p.score||0,kills:p.kills||0,deaths:p.deaths||0,shipType:p.shipType||"scout",ping:p.ping||0,mode:p.mode,partyId:p.partyId||null,factionId:p.factionId||null,factionTag:factionTagFor(p.factionId)};}

function broadcastWorldState(){
  const all=[ ...players.values()].map(snap);
  const projs=pvpProjectiles.map(p=>({id:p.id,x:p.x,y:p.y,vx:p.vx,vy:p.vy,ownerId:p.ownerId}));
  for(const[sid,p]of players){
    const nearby=all.filter(s=>s.id!==sid&&Math.hypot(s.x-p.x,s.y-p.y)<BROADCAST_RANGE);
    const nearProj=projs.filter(pr=>Math.hypot(pr.x-p.x,pr.y-p.y)<BROADCAST_RANGE);
    io.to(sid).emit("worldState",{self:snap(p),others:nearby,pvpProjectiles:nearProj});
    if(p.mode==="planet"&&p.planetId){
      const pps=[...players.values()].filter(o=>o.id!==sid&&o.mode==="planet"&&o.planetId===p.planetId).map(o=>({id:o.id,name:o.name,x:o.planetX||0,y:o.planetY||0,vx:o.planetVx||0,vy:o.planetVy||0,hp:o.hp,maxHp:o.maxHp,color:o.color,level:o.level,cosmeticColor:o.cosmeticColor,suitColor:o.suitColor,tool:o.planetTool||"mining",weaponLevel:o.weaponLevel||1}));
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

/* ── Main tick ── */
let lastTick=Date.now(),ecoTimer=0,lbTimer=0,slTimer=0,socialTimer=0;
setInterval(()=>{
  const now=Date.now(),dt=Math.min((now-lastTick)/1000,0.05);lastTick=now;
  economy.tick();tickPlayers(dt);tickProjectiles(dt);tickPlanetProjectiles(dt);tickOwnedStationDefense(dt);broadcastWorldState();
  ecoTimer+=dt;if(ecoTimer>=5){io.emit("economyUpdate",economy.snapshot());ecoTimer=0;}
  lbTimer+=dt; if(lbTimer>=10){broadcastLeaderboard();lbTimer=0;}
  slTimer+=dt; if(slTimer>=3){broadcastServerList();broadcastOwnedStationsList();slTimer=0;}
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
    if(!RES_KEYS.includes(type))continue;
    const q=Math.max(0,Math.min(999,Math.floor(Number(it.quantity)||0)));
    if(q>0)seen.set(type,(seen.get(type)||0)+q);
  }
  out.items=[...seen.entries()].map(([type,quantity])=>({type,quantity})).slice(0,12);
  return out;
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
  const oa=s.offers.a,ob=s.offers.b;
  if((pa.credits||0)<(oa.credits||0)||(pb.credits||0)<(ob.credits||0)){cancelTrade(s,"Trade cancelled: insufficient credits.");return;}
  if(!validateTradeItems(pa,oa.items)||!validateTradeItems(pb,ob.items)){cancelTrade(s,"Trade cancelled: one player no longer has the offered inventory.");return;}
  // Remove both offers first, then add received items. This prevents duplication exploits.
  for(const it of oa.items||[])removeInventory(pa,it.type,it.quantity);
  for(const it of ob.items||[])removeInventory(pb,it.type,it.quantity);
  for(const it of ob.items||[])addInventory(pa,it.type,it.quantity);
  for(const it of oa.items||[])addInventory(pb,it.type,it.quantity);
  pa.credits=pa.credits-(oa.credits||0)+(ob.credits||0);
  pb.credits=pb.credits-(ob.credits||0)+(oa.credits||0);
  tradeSessions.delete(s.id);
  syncAndPersist(pa,"trade_complete");syncAndPersist(pb,"trade_complete");
  io.to(pa.id).emit("tradeComplete",{tradeId:s.id,credits:pa.credits,gaveOffer:oa,receivedOffer:ob,otherName:pb.name,serverAuthoritative:true});
  io.to(pb.id).emit("tradeComplete",{tradeId:s.id,credits:pb.credits,gaveOffer:ob,receivedOffer:oa,otherName:pa.name,serverAuthoritative:true});
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

  socket.on("join",({name,token})=>{
    if(players.has(socket.id))return;
    const auth=verifyGameToken(token);
    const sp=computeSpawnPoint(),p=defaultPlayer(socket.id,auth?.displayName||name,sp.x,sp.y);
    applyAuthAccountToPlayer(p,auth);
    players.set(socket.id,p);
    if(p.memberId)socketsByMemberId.set(p.memberId,socket.id);
    socket.emit("welcome",{id:socket.id,memberId:p.memberId||null,x:p.x,y:p.y,color:p.color,galaxySeed:GALAXY_SEED,prices:economy.snapshot(),playerCount:players.size,shipTypes:SHIP_TYPES,ownedStationTiers:OWNED_STATION_TIERS,serverName:SERVER_NAME,credits:p.credits,maxSlots:p.maxSlots,invSlots:p.invSlots});
    emitInventorySync(p,"login");
    socket.broadcast.emit("playerJoined",{id:p.id,name:p.name,color:p.color});
    broadcastChat("Server",`${p.name} has entered the galaxy.`,"#78ff8a");
    broadcastLeaderboard();broadcastServerList();
    emitOwnedStationsList(socket);
  });

  socket.on("input",({rotLeft,rotRight,thrust,brake,shootX,shootY})=>{
    const p=players.get(socket.id);if(!p)return;
    p.input.rotLeft=!!rotLeft;p.input.rotRight=!!rotRight;p.input.thrust=!!thrust;p.input.brake=!!brake;
    if(shootX!==undefined&&p.input.shootX===null){p.input.shootX=shootX;p.input.shootY=shootY;}
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

  socket.on("modeChange",({mode,planetId,x,y})=>{
    const p=players.get(socket.id);if(!p)return;
    if(p.planetId)socket.leave(`planet:${p.planetId}`);
    p.mode=mode;p.planetId=planetId||null;if(p.planetId)socket.join(`planet:${p.planetId}`);if(x!==undefined){p.x=x;p.y=y;}
    if(mode==="space"){p.planetX=0;p.planetY=0;p.planetVx=0;p.planetVy=0;p.planetTool="mining";}
  });



  socket.on("requestPlanetMap",({planet})=>{
    const p=players.get(socket.id);if(!p)return;
    const map=getPlanetMap(planet);
    if(p.planetId)socket.leave(`planet:${p.planetId}`);
    p.mode="planet";p.planetId=map.planet.id;socket.join(`planet:${map.planet.id}`);
    socket.emit("planetMapState",{planetId:map.planet.id,W:map.W,H:map.H,tiles:Array.from(map.tiles),hp:Array.from(map.hp),heights:map.heights});
  });

  socket.on("minePlanetTile",({planetId,tx,ty,power})=>{
    const p=players.get(socket.id);if(!p||p.mode!=="planet"||p.planetId!==planetId)return;
    const map=planetMaps.get(planetId);if(!map)return;
    tx=Math.floor(Number(tx));ty=Math.floor(Number(ty));
    if(tx<0||ty<0||tx>=map.W||ty>=map.H-3)return;
    const id=ty*map.W+tx,t=map.tiles[id];
    if(!t||t===PLANET_TILE.BEDROCK)return;
    const dmg=Math.max(1,Math.min(40,Number(power)||18));
    map.hp[id]=Math.max(0,map.hp[id]-dmg);
    if(map.hp[id]<=0){
      const kind=planetResForTile(map.planet,t,ty,map.H),rar=RES_RARITY[kind]||1;
      map.tiles[id]=0;map.hp[id]=0;
      io.to(`planet:${planetId}`).emit("planetTileUpdate",{planetId,tx,ty,tile:0,hp:0});
      const qty=(t===3||t===4)?(Math.random()<0.35?2:1):(t===5?(Math.random()<0.55?2:1):1);
      addInventory(p,kind,qty);
      const dropX=tx*16+8,dropY=ty*16+8;
      // Broadcast a visible, shared loot pop to everyone on this planet.
      // Inventory remains server-authoritative and is granted immediately below.
      io.to(`planet:${planetId}`).emit("planetMineDrop",{planetId,kind,x:dropX,y:dropY,qty,ownerId:p.id});
      socket.emit("planetMineReward",{planetId,kind,x:dropX,y:dropY,qty});
      syncAndPersist(p,"planet_mine");
      grantXp(p,rar*2,"Mining");
    }else{
      io.to(`planet:${planetId}`).emit("planetTileUpdate",{planetId,tx,ty,tile:t,hp:map.hp[id]});
    }
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
    const raw=planetWeaponDamage(p), armor=1+((t.attrs.armor-1)*0.08), dmg=raw/armor;
    t.hp=Math.max(0,t.hp-dmg);t.lastPlanetAttacker=p.id;
    socket.emit("planetAttackConfirm",{targetId:t.id,damage:Math.round(dmg),hp:t.hp});
    io.to(t.id).emit("planetHit",{damage:Math.round(dmg),hp:t.hp,attackerName:p.name});
    if(t.hp<=0){
      t.deaths=(t.deaths||0)+1;p.kills=(p.kills||0)+1;p.credits+=75;addScore(p,250,"Planet PvP");
      io.to(p.id).emit("creditUpdate",{credits:p.credits});
      io.to(t.id).emit("youDied",{killedBy:p.name});
      io.emit("playerKilled",{victimId:t.id,victimName:t.name,killerId:p.id,killerName:p.name});
      setTimeout(()=>{const rp=players.get(t.id);if(!rp)return;if(rp.planetId)io.sockets.sockets.get(t.id)?.leave(`planet:${rp.planetId}`);const sp=computeSpawnPoint();rp.mode="space";rp.planetId=null;rp.x=sp.x;rp.y=sp.y;rp.hp=rp.maxHp;rp.shield=rp.maxShield;rp.energy=100;rp.planetX=0;rp.planetY=0;io.to(t.id).emit("respawn",{x:rp.x,y:rp.y});},3000);
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
    p.planetShootAt=now+520;
    planetProjectiles.push({id:`pp_${p.id}_${now}_${Math.floor(Math.random()*9999)}`,planetId,ownerId:p.id,ownerName:p.name,x,y,vx:Math.cos(ang)*PLANET_PROJ_SPEED,vy:Math.sin(ang)*PLANET_PROJ_SPEED,damage:planetWeaponDamage(p),life:PLANET_PROJ_LIFE});
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
    s.offers[side]=clean;
    s.ready.a=false;s.ready.b=false;
    emitTradeState(s);
  });

  socket.on("tradeReady",({tradeId,ready})=>{
    const p=players.get(socket.id),s=tradeSessions.get(tradeId);if(!p||!s)return;
    const side=sideOfTrade(s,p.id);if(!side)return;
    s.offers[side]=sanitizeTradeOffer(s.offers[side],p);
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
    const dmg=Math.max(1,Math.min(30,Number(damage)||7));
    p.hp=Math.max(0,p.hp-dmg);
    socket.emit("oxygenDamageUpdate",{hp:p.hp,damage:dmg});
    if(p.hp<=0){
      p.deaths=(p.deaths||0)+1;
      socket.emit("youDied",{killedBy:"Oxygen Depletion"});
      setTimeout(()=>{const rp=players.get(socket.id);if(!rp)return;const sp=computeSpawnPoint();rp.mode="space";rp.planetId=null;rp.x=sp.x;rp.y=sp.y;rp.hp=rp.maxHp;rp.shield=rp.maxShield;rp.energy=100;socket.emit("respawn",{x:rp.x,y:rp.y});},3000);
    }
  });

  socket.on("requestInventorySync",()=>{const p=players.get(socket.id);if(p)emitInventorySync(p,"requested");});

  socket.on("buyInventorySlot",()=>{
    const p=players.get(socket.id);if(!p)return;
    const SLOT_COST=1000,MAX_TOTAL_SLOTS=96;
    if((p.maxSlots||24)>=MAX_TOTAL_SLOTS){socket.emit("inventorySlotDenied",{reason:"Maximum slots reached."});return;}
    if((p.credits||0)<SLOT_COST){socket.emit("inventorySlotDenied",{reason:`Need ${SLOT_COST}cr.`});return;}
    p.credits-=SLOT_COST;p.maxSlots=(p.maxSlots||24)+1;p.invSlots.push({type:null,count:0});
    socket.emit("inventorySlotConfirm",{credits:p.credits,maxSlots:p.maxSlots});syncAndPersist(p,"buy_inventory_slot");
  });

  socket.on("sell",({resourceType,quantity})=>{
    const p=players.get(socket.id);if(!p||quantity<=0||quantity>500)return;
    const pr=economy.price(resourceType);if(!pr)return;
    quantity=Math.floor(Number(quantity)||0);
    if(!removeInventory(p,resourceType,quantity)){socket.emit("sellDenied",{reason:"You do not have that quantity in your server inventory."});return;}
    const earned=pr*quantity;p.credits+=earned;p.tradingVolume=(p.tradingVolume||0)+earned;
    economy.sold(resourceType,quantity);addScore(p,Math.floor(earned*0.1),"Trade");
    socket.emit("sellConfirm",{resourceType,quantity,earned,credits:p.credits,prices:economy.snapshot()});
    syncAndPersist(p,"sell_resource");
  });

  socket.on("buy",({resourceType,quantity,pricePerUnit})=>{
    const p=players.get(socket.id);if(!p||quantity<=0||quantity>500)return;
    resourceType=String(resourceType||"");
    quantity=Math.floor(Number(quantity)||0);
    if(!RES_KEYS.includes(resourceType)||quantity<=0)return;

    // Never allow buy prices below the global sell value, or players can buy low
    // and immediately sell high. Client station stock now also uses this floor.
    const marketPrice=economy.price(resourceType);
    const quotedPrice=Math.floor(Number(pricePerUnit)||0);
    const minAllowed=Math.max(1,Math.ceil(marketPrice*1.08));
    const maxAllowed=Math.max(minAllowed,Math.ceil(marketPrice*6.0));
    const unitPrice=quotedPrice>0?quotedPrice:minAllowed;
    if(unitPrice<minAllowed||unitPrice>maxAllowed){
      socket.emit("buyDenied",{reason:"Price changed. Retry."});return;
    }

    const cost=unitPrice*quantity;if(p.credits<cost){socket.emit("buyDenied",{reason:"Insufficient credits."});return;}
    if(!canFitInventory(p,resourceType,quantity)){socket.emit("buyDenied",{reason:"Inventory full."});return;}
    p.credits-=cost;economy.bought(resourceType,quantity);addInventory(p,resourceType,quantity);
    socket.emit("buyConfirm",{resourceType,quantity,cost,credits:p.credits,prices:economy.snapshot()});
    syncAndPersist(p,"buy_resource");
  });

  socket.on("buyShip",({shipTypeKey})=>{
    const p=players.get(socket.id);if(!p)return;
    const def=SHIP_TYPES[shipTypeKey];
    if(!def){socket.emit("shipBuyDenied",{reason:"Unknown ship."});return;}
    if(def.craftOnly||def.recipe){socket.emit("shipBuyDenied",{reason:"This ship must be crafted from parts."});return;}
    if(p.shipType===shipTypeKey){socket.emit("shipBuyDenied",{reason:"Already own this ship."});return;}
    if(p.credits<def.price){socket.emit("shipBuyDenied",{reason:`Need ${def.price}cr.`});return;}
    p.credits-=def.price;p.shipType=shipTypeKey;p.maxHp=def.maxHp;p.hp=def.maxHp;p.maxShield=def.maxShield;p.shield=def.maxShield;
    socket.emit("shipBuyConfirm",{shipTypeKey,credits:p.credits,hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield});
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
    p.shipType=shipTypeKey;p.maxHp=def.maxHp;p.hp=def.maxHp;p.maxShield=def.maxShield;p.shield=def.maxShield;
    socket.emit("craftShipConfirm",{shipTypeKey,credits:p.credits,hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield,invSlots:p.invSlots,maxSlots:p.maxSlots});
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

  socket.on("buyStation",({x,y,tier})=>{
    const p=players.get(socket.id);if(!p)return;
    const td=OWNED_STATION_TIERS[tier];if(!td){socket.emit("stationBuyDenied",{reason:"Unknown tier."});return;}
    if(p.credits<td.price){socket.emit("stationBuyDenied",{reason:`Need ${td.price}cr.`});return;}
    const key=`${Math.round(x/100)}_${Math.round(y/100)}`;
    if(ownedStations.has(key)){socket.emit("stationBuyDenied",{reason:"Location occupied."});return;}
    p.credits-=td.price;syncAndPersist(p,"buy_station");
    const st={key,ownerId:p.id,ownerName:p.name,x,y,tier,hiredShips:[],accumulatedGoods:{},...makeStationState(tier)};
    ownedStations.set(key,st);addScore(p,1000,"Station Built");
    socket.emit("stationBuyConfirm",{key,x,y,tier,credits:p.credits});
    broadcastOwnedStationsList();
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
    socket.emit("hireConfirm",{stationKey,shipCount:st.hiredShips.length,credits:p.credits});
    socket.emit("creditUpdate",{credits:p.credits});
    broadcastOwnedStationsList();
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
    const p=players.get(socket.id);if(!p||p.mode!=="space")return;
    const raw=Math.max(0,Math.min(90,Number(damage)||0));if(raw<=0)return;
    const armor=1+((p.attrs.armor-1)*0.2);let dmg=raw/armor;
    if(p.shield>0){const abs=Math.min(p.shield,dmg);p.shield-=abs;dmg-=abs;}
    p.hp=Math.max(0,p.hp-dmg);
    // NPC/trade-ship hits should pause regen long enough to let sustained fire matter.
    p.shieldRegenTimer=5;
    socket.emit("hit",{damage:Math.round(raw/armor),hp:p.hp,shield:p.shield,by:source||"Trade Ship"});
    if(p.hp<=0){
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
    socket.emit("oxygenTankUsed",{});syncAndPersist(p,"use_oxygen_tank");
  });

  socket.on("useGas",()=>{
    const p=players.get(socket.id);if(!p)return;
    if(!removeInventory(p,"gas_canister",1)){socket.emit("useItemDenied",{type:"gas_canister",reason:"No gas canister in server inventory."});return;}
    p.energy=Math.min(100,p.energy+GAS_REFUEL);socket.emit("energyUpdate",{energy:p.energy});syncAndPersist(p,"use_gas");
  });

  socket.on("upgradeAttr",({attr})=>{
    const p=players.get(socket.id);if(!p)return;
    const valid=["damage","speed","armor","gasEfficiency","shieldRegen"];
    if(!valid.includes(attr))return;
    if((p.attrPoints||0)<=0){socket.emit("upgradeDenied",{reason:"No attribute points. Use paid upgrade instead."});return;}
    if((p.attrs[attr]||1)>=10){socket.emit("upgradeDenied",{reason:"Already maxed."});return;}
    p.attrs[attr]=(p.attrs[attr]||1)+1;p.attrPoints=(p.attrPoints||0)-1;
    socket.emit("attrConfirm",{attr,val:p.attrs[attr],attrPoints:p.attrPoints,credits:p.credits,xp:p.xp,level:p.level});syncAndPersist(p,"upgrade_attr");
  });

  socket.on("upgradeAttrPaid",({attr})=>{
    const p=players.get(socket.id);if(!p)return;
    const valid=["damage","speed","armor","gasEfficiency","shieldRegen"];
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

  socket.on("clientPing",()=>{
    const p=players.get(socket.id);if(!p)return;
    const now=Date.now();if(p.pingTs)p.ping=Math.min(999,now-p.pingTs);p.pingTs=now;
    socket.emit("serverPong");
  });

  socket.on("requestLeaderboard",()=>socket.emit("leaderboard",buildLeaderboard(10)));
  socket.on("requestServerList",()=>socket.emit("serverList",{name:SERVER_NAME,players:[...players.values()].map(serverListSnap),uptime:Math.floor((Date.now()-SERVER_START)/1000)}));
  socket.on("requestOwnedStations",()=>emitOwnedStationsList(socket));

  socket.on("disconnect",()=>{
    const p=players.get(socket.id);
    if(p){broadcastChat("Server",`${p.name} has left the galaxy.`,"#ff8888");socket.broadcast.emit("playerLeft",{id:socket.id});persistPlayerNow(p,"disconnect");if(p.memberId)socketsByMemberId.delete(p.memberId);}
    for(const ts of [...tradeSessions.values()])if(ts.a===socket.id||ts.b===socket.id)cancelTrade(ts,"Trade cancelled: player disconnected.");
    if(p?.partyId)leaveParty(socket.id,"Disconnected from party.");
    if(p?.factionId){const f=factions.get(p.factionId);if(f)emitFactionState(f.id);}
    players.delete(socket.id);broadcastLeaderboard();broadcastServerList();
  });
});

const PORT=process.env.PORT||3000;
server.listen(PORT,()=>{console.log(`🚀 ${SERVER_NAME} on port ${PORT} | ${TICK_RATE}Hz | Max:${MAX_PLAYERS}`);});


