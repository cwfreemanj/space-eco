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
  res.setHeader("Access-Control-Allow-Headers", "Content-Type");
  if (req.method === "OPTIONS") { res.sendStatus(204); return; }
  next();
});

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

const RES_KEYS=["dirt","stone","copper","iron","gold","crystal","fuel","gas_canister","ice_block","lava_rock","magma_core","toxic_sludge","sand","grass_tuft"];
const RES_BASE={dirt:1,stone:3,copper:9,iron:10,gold:40,crystal:60,fuel:25,gas_canister:30,ice_block:4,lava_rock:12,magma_core:22,toxic_sludge:8,sand:2,grass_tuft:1};
const RES_RARITY={dirt:1,stone:2,copper:3,iron:3,gold:5,crystal:6,fuel:4,gas_canister:2,ice_block:2,lava_rock:3,magma_core:4,toxic_sludge:3,sand:1,grass_tuft:1};
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
    shipCount:st.hiredShips.length,
    ships:st.hiredShips.map(sh=>({id:sh.id,state:sh.state||"collecting"})),
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
    if(st.hiredShips.length===0)continue;
    for(const ship of st.hiredShips){
      const count=2+Math.floor(Math.random()*6);
      for(let i=0;i<count;i++){const r=RESOURCES[Math.floor(Math.random()*RESOURCES.length)];st.accumulatedGoods[r]=(st.accumulatedGoods[r]||0)+1;}
    }
    const owner=players.get(st.ownerId);
    if(owner)io.to(st.ownerId).emit("ownedStationUpdate",{stationKey:st.key,goodsCount:Object.values(st.accumulatedGoods).reduce((a,b)=>a+b,0),shipCount:st.hiredShips.length});
  }
},30000);

/* ── Main tick ── */
let lastTick=Date.now(),ecoTimer=0,lbTimer=0,slTimer=0;
setInterval(()=>{
  const now=Date.now(),dt=Math.min((now-lastTick)/1000,0.05);lastTick=now;
  economy.tick();tickPlayers(dt);tickProjectiles(dt);broadcastWorldState();
  ecoTimer+=dt;if(ecoTimer>=5){io.emit("economyUpdate",economy.snapshot());ecoTimer=0;}
  lbTimer+=dt; if(lbTimer>=10){broadcastLeaderboard();lbTimer=0;}
  slTimer+=dt; if(slTimer>=3){broadcastServerList();slTimer=0;}
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
    p.mode=mode;p.planetId=planetId||null;if(x!==undefined){p.x=x;p.y=y;}
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
    const st={key,ownerId:p.id,ownerName:p.name,x,y,tier,hiredShips:[],accumulatedGoods:{}};
    ownedStations.set(key,st);addScore(p,1000,"Station Built");
    socket.emit("stationBuyConfirm",{key,x,y,tier,credits:p.credits});
    broadcastOwnedStationsList();
    broadcastChat("Server",`${p.name} built a ${td.name} at (${Math.round(x)}, ${Math.round(y)})!`,"#ffcc44");
  });

  socket.on("hireShip",({stationKey})=>{
    const p=players.get(socket.id);if(!p)return;
    const st=ownedStations.get(stationKey);if(!st||st.ownerId!==p.id){socket.emit("hireDenied",{reason:"Not your station."});return;}
    const td=OWNED_STATION_TIERS[st.tier];
    if(st.hiredShips.length>=td.maxShips){socket.emit("hireDenied",{reason:`Max ${td.maxShips} ships.`});return;}
    if(p.credits<td.shipHireCost){socket.emit("hireDenied",{reason:`Need ${td.shipHireCost}cr.`});return;}
    p.credits-=td.shipHireCost;
    st.hiredShips.push({id:`os_${stationKey}_${Date.now()}_${Math.floor(Math.random()*9999)}`,state:"collecting",cargo:{},createdAt:Date.now()});
    socket.emit("hireConfirm",{stationKey,shipCount:st.hiredShips.length,credits:p.credits});
    socket.emit("creditUpdate",{credits:p.credits});
    broadcastOwnedStationsList();
  });

  socket.on("collectOwnedStation",({stationKey})=>{
    const p=players.get(socket.id);if(!p)return;
    const st=ownedStations.get(stationKey);if(!st||st.ownerId!==p.id)return;
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
    st.hiredShips.splice(idx,1);
    addScore(p,75,"Trade Ship Destroyed");
    socket.emit("ownedTradeShipDestroyConfirm",{stationKey,shipId});
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
