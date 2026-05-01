/**
 * Space Eco — Multiplayer Server v2
 * Adds: scores · leaderboard · ship types · owned stations · coord tracking · server list
 */

const express = require("express");
const http    = require("http");
const { Server } = require("socket.io");
const path    = require("path");

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
  credits_1000_test: { credits:1000, amount:0.50, cents:50, label:"Small Credit Drop" },
  credits_10000:   { credits:10000,   amount:1.99,  cents:199,  label:"Scout Cache" },
  credits_25000:   { credits:25000,   amount:2.99,  cents:299,  label:"Trader Pack" },
  credits_50000:   { credits:50000,   amount:3.99,  cents:399,  label:"Fleet Boost" },
  credits_100000:  { credits:100000,  amount:4.99,  cents:499,  label:"Station Builder" },
  credits_500000:  { credits:500000,  amount:19.99, cents:1999, label:"Empire Vault" },
  credits_1000000: { credits:1000000, amount:49.99, cents:4999, label:"Galaxy Treasury" },
};
const grantedCreditPayments = new Map(); // paymentId -> grant record
const PURCHASE_WEBHOOK_SECRET = process.env.PURCHASE_WEBHOOK_SECRET || "";

/* ── Ship types (synced to client) ── */
const SHIP_TYPES = {
  scout:       { name:"Scout",       price:0,     description:"Starter ship. Fast and agile.",           maxHp:100, maxShield:60,  thrustMult:1.00, cargoMult:1.0, damageMult:1.0, shieldRegenMult:1.0, size:"small"  },
  hauler:      { name:"Hauler",      price:2500,  description:"Massive cargo hold. Built for trading.",  maxHp:160, maxShield:40,  thrustMult:0.70, cargoMult:2.2, damageMult:0.8, shieldRegenMult:0.8, size:"large"  },
  fighter:     { name:"Fighter",     price:3500,  description:"Combat-focused with strong weapons.",     maxHp:130, maxShield:80,  thrustMult:1.15, cargoMult:0.7, damageMult:1.8, shieldRegenMult:1.2, size:"medium" },
  interceptor: { name:"Interceptor", price:5000,  description:"Extreme speed. Fragile but deadly fast.", maxHp:80,  maxShield:50,  thrustMult:1.60, cargoMult:0.5, damageMult:1.3, shieldRegenMult:1.5, size:"small"  },
  dreadnought: { name:"Dreadnought", price:12000, description:"Tanky powerhouse. Slow but devastating.", maxHp:280, maxShield:150, thrustMult:0.55, cargoMult:1.5, damageMult:2.2, shieldRegenMult:0.7, size:"huge"   },
  phantom:     { name:"Phantom",     price:8000,  description:"Balanced stealth raider.",               maxHp:110, maxShield:90,  thrustMult:1.30, cargoMult:0.9, damageMult:1.5, shieldRegenMult:1.4, size:"medium" },
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
  };
}

function sanitizeName(raw) { return String(raw||"Pilot").replace(/[^a-zA-Z0-9_ \-]/g,"").slice(0,16).trim()||"Pilot"; }
function randomShipColor() { const p=["#7be6ff","#ff9944","#66ff88","#ff66aa","#ffdd44","#cc88ff","#44ccff","#ff6644"]; return p[Math.floor(Math.random()*p.length)]; }

/* ── Score ── */
function addScore(player, amount, reason) {
  player.score = (player.score||0) + amount;
  io.to(player.id).emit("scoreUpdate", { score:player.score, delta:amount, reason });
}
function grantXp(player,amount,reason="Mining/Combat"){
  if(!player||amount<=0)return;
  player.xp=(player.xp||0)+amount;player.miningScore=(player.miningScore||0)+amount;
  addScore(player,Math.floor(amount*0.5),reason);
  const xtn=Math.floor(100*Math.pow(1.4,player.level-1));
  if(player.xp>=xtn){player.xp-=xtn;player.level++;player.attrPoints=(player.attrPoints||0)+2;io.to(player.id).emit("levelUp",{level:player.level,attrPoints:player.attrPoints});}
  io.to(player.id).emit("xpUpdate",{xp:player.xp,level:player.level});
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

const RES_KEYS=["dirt","stone","copper","iron","gold","crystal","fuel","gas_canister","oxygen_tank","ice_block","lava_rock","magma_core","toxic_sludge","sand","grass_tuft"];
const RES_BASE={dirt:1,stone:3,copper:9,iron:10,gold:40,crystal:60,fuel:25,gas_canister:30,oxygen_tank:35,ice_block:4,lava_rock:12,magma_core:22,toxic_sludge:8,sand:2,grass_tuft:1};
const RES_RARITY={dirt:1,stone:2,copper:3,iron:3,gold:5,crystal:6,fuel:4,gas_canister:2,oxygen_tank:2,ice_block:2,lava_rock:3,magma_core:4,toxic_sludge:3,sand:1,grass_tuft:1};
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


/* ── Persistent planet maps ──
   These maps live on the server so one planet has one shared, mineable state.
   They reset only when the Railway process restarts. Persist to Wix/DB later for permanent worlds.
*/
const PLANET_TILE={EMPTY:0,DIRT:1,STONE:2,ORE1:3,ORE2:4,RARE:5,ICE:6,PACKED_ICE:7,LAVA:8,MAGMA:9,TOXIC_SLUDGE:10,SAND:11,SANDSTONE:12,GRASS:13,BEDROCK:14};
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
  const grant={paymentId,packageId,socketId,playerName:p.name,creditsAdded:pack.credits,credits:p.credits,grantedAt:Date.now()};
  grantedCreditPayments.set(paymentId,grant);
  addScore(p,Math.floor(pack.credits*0.002),"Credit Purchase");
  io.to(socketId).emit("creditPurchaseConfirm",grant);
  io.to(socketId).emit("creditUpdate",{credits:p.credits});
  res.json({ok:true,grant});
});

/* ── PvP projectiles ── */
const pvpProjectiles=[];
const SHOOT_CD=0.22, PROJ_SPEED=280, PROJ_LIFE=2.2, BASE_DAMAGE=18;

function tickProjectiles(dt){
  for(let i=pvpProjectiles.length-1;i>=0;i--){
    const p=pvpProjectiles[i];p.x+=p.vx*dt;p.y+=p.vy*dt;p.life-=dt;
    if(p.life<=0){pvpProjectiles.splice(i,1);continue;}
    for(const[sid,target]of players){
      if(sid===p.ownerId||target.mode!=="space")continue;
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
function snap(p){return{id:p.id,name:p.name,x:p.x,y:p.y,vx:p.vx,vy:p.vy,angle:p.angle,hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield,shieldRegenTimer:p.shieldRegenTimer||0,color:p.color,level:p.level,mode:p.mode,score:p.score||0,kills:p.kills||0,shipType:p.shipType||"scout",ping:p.ping||0};}
function serverListSnap(p){return{id:p.id,name:p.name,x:Math.round(p.x),y:Math.round(p.y),level:p.level,score:p.score||0,kills:p.kills||0,deaths:p.deaths||0,shipType:p.shipType||"scout",ping:p.ping||0,mode:p.mode};}

function broadcastWorldState(){
  const all=[ ...players.values()].map(snap);
  const projs=pvpProjectiles.map(p=>({id:p.id,x:p.x,y:p.y,vx:p.vx,vy:p.vy,ownerId:p.ownerId}));
  for(const[sid,p]of players){
    const nearby=all.filter(s=>s.id!==sid&&Math.hypot(s.x-p.x,s.y-p.y)<BROADCAST_RANGE);
    const nearProj=projs.filter(pr=>Math.hypot(pr.x-p.x,pr.y-p.y)<BROADCAST_RANGE);
    io.to(sid).emit("worldState",{self:snap(p),others:nearby,pvpProjectiles:nearProj});
  }
}

function broadcastLeaderboard(){io.emit("leaderboard",buildLeaderboard(10));}
function broadcastServerList(){io.emit("serverList",{name:SERVER_NAME,players:[...players.values()].map(serverListSnap),uptime:Math.floor((Date.now()-SERVER_START)/1000)});}
function broadcastChat(from,message,color){io.emit("chat",{from,message:String(message).replace(/</g,"&lt;").slice(0,120),color:color||"#d6e1ff",ts:Date.now()});}

/* ── Owned stations ── */
const ownedStations=new Map();

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
let lastTick=Date.now(),ecoTimer=0,lbTimer=0,slTimer=0;
setInterval(()=>{
  const now=Date.now(),dt=Math.min((now-lastTick)/1000,0.05);lastTick=now;
  economy.tick();tickPlayers(dt);tickProjectiles(dt);tickOwnedStationDefense(dt);broadcastWorldState();
  ecoTimer+=dt;if(ecoTimer>=5){io.emit("economyUpdate",economy.snapshot());ecoTimer=0;}
  lbTimer+=dt; if(lbTimer>=10){broadcastLeaderboard();lbTimer=0;}
  slTimer+=dt; if(slTimer>=3){broadcastServerList();broadcastOwnedStationsList();slTimer=0;}
},TICK_MS);

/* ── Socket events ── */
io.on("connection",socket=>{
  if(players.size>=MAX_PLAYERS){socket.emit("serverFull");socket.disconnect(true);return;}

  socket.on("join",({name})=>{
    if(players.has(socket.id))return;
    const sp=computeSpawnPoint(),p=defaultPlayer(socket.id,name,sp.x,sp.y);
    players.set(socket.id,p);
    socket.emit("welcome",{id:socket.id,x:p.x,y:p.y,color:p.color,galaxySeed:GALAXY_SEED,prices:economy.snapshot(),playerCount:players.size,shipTypes:SHIP_TYPES,ownedStationTiers:OWNED_STATION_TIERS,serverName:SERVER_NAME});
    socket.broadcast.emit("playerJoined",{id:p.id,name:p.name,color:p.color});
    broadcastChat("Server",`${p.name} has entered the galaxy.`,"#78ff8a");
    broadcastLeaderboard();broadcastServerList();
    // Send owned stations list
    emitOwnedStationsList(socket);
  });

  socket.on("input",({rotLeft,rotRight,thrust,brake,shootX,shootY})=>{
    const p=players.get(socket.id);if(!p)return;
    p.input.rotLeft=!!rotLeft;p.input.rotRight=!!rotRight;p.input.thrust=!!thrust;p.input.brake=!!brake;
    if(shootX!==undefined&&p.input.shootX===null){p.input.shootX=shootX;p.input.shootY=shootY;}
  });

  socket.on("modeChange",({mode,planetId,x,y})=>{
    const p=players.get(socket.id);if(!p)return;
    if(p.planetId)socket.leave(`planet:${p.planetId}`);
    p.mode=mode;p.planetId=planetId||null;if(p.planetId)socket.join(`planet:${p.planetId}`);if(x!==undefined){p.x=x;p.y=y;}
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
      socket.emit("planetMineDrop",{planetId,kind,x:tx*16+8,y:ty*16+8,qty});
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
    map.tiles[id]=tile;map.hp[id]=hpForPlacedTile(tile);
    io.to(`planet:${planetId}`).emit("planetTileUpdate",{planetId,tx,ty,tile,hp:map.hp[id]});
  });

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

  socket.on("sell",({resourceType,quantity})=>{
    const p=players.get(socket.id);if(!p||quantity<=0||quantity>500)return;
    const pr=economy.price(resourceType);if(!pr)return;
    const earned=pr*quantity;p.credits+=earned;p.tradingVolume=(p.tradingVolume||0)+earned;
    economy.sold(resourceType,quantity);addScore(p,Math.floor(earned*0.1),"Trade");
    socket.emit("sellConfirm",{resourceType,quantity,earned,credits:p.credits,prices:economy.snapshot()});
  });

  socket.on("buy",({resourceType,quantity,pricePerUnit})=>{
    const p=players.get(socket.id);if(!p||quantity<=0||quantity>500)return;
    const sp2=economy.price(resourceType);
    if(Math.abs(pricePerUnit-sp2)/sp2>0.25){socket.emit("buyDenied",{reason:"Price changed. Retry."});return;}
    const cost=sp2*quantity;if(p.credits<cost){socket.emit("buyDenied",{reason:"Insufficient credits."});return;}
    p.credits-=cost;economy.bought(resourceType,quantity);
    socket.emit("buyConfirm",{resourceType,quantity,cost,credits:p.credits,prices:economy.snapshot()});
  });

  socket.on("buyShip",({shipTypeKey})=>{
    const p=players.get(socket.id);if(!p)return;
    const def=SHIP_TYPES[shipTypeKey];
    if(!def){socket.emit("shipBuyDenied",{reason:"Unknown ship."});return;}
    if(p.shipType===shipTypeKey){socket.emit("shipBuyDenied",{reason:"Already own this ship."});return;}
    if(p.credits<def.price){socket.emit("shipBuyDenied",{reason:`Need ${def.price}cr.`});return;}
    p.credits-=def.price;p.shipType=shipTypeKey;p.maxHp=def.maxHp;p.hp=def.maxHp;p.maxShield=def.maxShield;p.shield=def.maxShield;
    socket.emit("shipBuyConfirm",{shipTypeKey,credits:p.credits,hp:p.hp,maxHp:p.maxHp,shield:p.shield,maxShield:p.maxShield});
    broadcastChat("Server",`${p.name} upgraded to a ${def.name}!`,"#ffdd44");
  });

  socket.on("buyStation",({x,y,tier})=>{
    const p=players.get(socket.id);if(!p)return;
    const td=OWNED_STATION_TIERS[tier];if(!td){socket.emit("stationBuyDenied",{reason:"Unknown tier."});return;}
    if(p.credits<td.price){socket.emit("stationBuyDenied",{reason:`Need ${td.price}cr.`});return;}
    const key=`${Math.round(x/100)}_${Math.round(y/100)}`;
    if(ownedStations.has(key)){socket.emit("stationBuyDenied",{reason:"Location occupied."});return;}
    p.credits-=td.price;
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
    p.credits-=td.shipHireCost;
    st.hiredShips.push({id:`os_${stationKey}_${Date.now()}_${Math.floor(Math.random()*9999)}`,state:(Date.now()<(st.underAttackUntil||0)?"defending":"collecting"),cargo:{},createdAt:Date.now(),respawnAt:0});
    socket.emit("hireConfirm",{stationKey,shipCount:st.hiredShips.length,credits:p.credits});
    socket.emit("creditUpdate",{credits:p.credits});
    broadcastOwnedStationsList();
  });

  socket.on("collectOwnedStation",({stationKey})=>{
    const p=players.get(socket.id);if(!p)return;
    const st=ownedStations.get(stationKey);if(!st||st.ownerId!==p.id||st.destroyed)return;
    socket.emit("ownedStationGoods",{stationKey,goods:{...st.accumulatedGoods}});
    st.accumulatedGoods={};
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

  socket.on("useGas",()=>{
    const p=players.get(socket.id);if(!p)return;
    p.energy=Math.min(100,p.energy+GAS_REFUEL);socket.emit("energyUpdate",{energy:p.energy});
  });

  socket.on("upgradeAttr",({attr})=>{
    const p=players.get(socket.id);if(!p)return;
    const valid=["damage","speed","cargoMax","armor","gasEfficiency","shieldRegen"];
    if(!valid.includes(attr))return;
    if((p.attrPoints||0)<=0){socket.emit("upgradeDenied",{reason:"No attribute points."});return;}
    if((p.attrs[attr]||1)>=10){socket.emit("upgradeDenied",{reason:"Already maxed."});return;}
    p.attrs[attr]=(p.attrs[attr]||1)+1;p.attrPoints=(p.attrPoints||0)-1;
    socket.emit("attrConfirm",{attr,val:p.attrs[attr],attrPoints:p.attrPoints});
  });

  socket.on("gainXp",({amount})=>{
    const p=players.get(socket.id);if(!p||amount<=0||amount>500)return;
    p.xp=(p.xp||0)+amount;p.miningScore=(p.miningScore||0)+amount;
    addScore(p,Math.floor(amount*0.5),"Mining/Combat");
    const xtn=Math.floor(100*Math.pow(1.4,p.level-1));
    if(p.xp>=xtn){p.xp-=xtn;p.level++;p.attrPoints=(p.attrPoints||0)+2;socket.emit("levelUp",{level:p.level,attrPoints:p.attrPoints});}
    socket.emit("xpUpdate",{xp:p.xp,level:p.level});
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
    if(p){broadcastChat("Server",`${p.name} has left the galaxy.`,"#ff8888");socket.broadcast.emit("playerLeft",{id:socket.id});}
    players.delete(socket.id);broadcastLeaderboard();broadcastServerList();
  });
});

const PORT=process.env.PORT||3000;
server.listen(PORT,()=>{console.log(`🚀 ${SERVER_NAME} on port ${PORT} | ${TICK_RATE}Hz | Max:${MAX_PLAYERS}`);});
