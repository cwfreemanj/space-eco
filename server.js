/**
 * Space Eco — Multiplayer Server
 * Node.js + Socket.io, authoritative positions, 20Hz tick
 * Deploy on Railway / Render / Fly.io
 */

const express = require("express");
const http    = require("http");
const { Server } = require("socket.io");
const path    = require("path");

const app    = express();
const server = http.createServer(app);
const io     = new Server(server, {
  cors: { origin: "*", methods: ["GET","POST"] },
  pingTimeout:  20000,
  pingInterval: 10000
});

// Serve the game client from the same process (optional convenience)
app.use(express.static(path.join(__dirname, "public")));
app.get("/", (_req, res) => res.sendFile(path.join(__dirname, "public", "index.html")));

/* ═══════════════════════════════════════════
   CONSTANTS
═══════════════════════════════════════════ */
const TICK_RATE      = 20;          // Hz  — server broadcast rate
const TICK_MS        = 1000 / TICK_RATE;
const CHUNK_SIZE     = 900;         // must match client
const SPAWN_RADIUS   = 600;         // new players spawn within this radius of active cluster
const DEAD_ZONE      = 300;         // min distance from origin to spawn
const BROADCAST_RANGE = CHUNK_SIZE * 3.5; // only send other players within this range
const MAX_PLAYERS    = 200;         // hard cap

/* ═══════════════════════════════════════════
   GALAXY SEED  (shared with client)
═══════════════════════════════════════════ */
const GALAXY_SEED = "GALAXY-01";

/* ═══════════════════════════════════════════
   PLAYER STATE
═══════════════════════════════════════════ */
const players = new Map();   // socketId → playerState
const recentSpawnPoints = []; // circular buffer of recent positions for spawn proximity

function defaultPlayer(id, name, x, y) {
  return {
    id,
    name: sanitizeName(name),
    x, y,
    vx: 0, vy: 0,
    angle: 0,
    hp: 100, maxHp: 100,
    shield: 60, maxShield: 60,
    level: 1,
    credits: 300,
    color: randomShipColor(),
    // Input snapshot from client (processed server-side)
    input: { rotLeft:false, rotRight:false, thrust:false, brake:false, shootX:null, shootY:null },
    shootCooldown: 0,
    lastSeen: Date.now(),
    mode: "space",          // "space" | "planet"
    planetId: null,
    attrs: { damage:1, speed:1, cargoMax:1, armor:1, gasEfficiency:1, shieldRegen:1 },
    energy: 100,
    shieldRegenTimer: 0,
  };
}

function sanitizeName(raw) {
  return String(raw || "Pilot").replace(/[^a-zA-Z0-9_ \-]/g, "").slice(0, 16).trim() || "Pilot";
}

function randomShipColor() {
  const palette = ["#7be6ff","#ff9944","#66ff88","#ff66aa","#ffdd44","#cc88ff","#44ccff","#ff6644"];
  return palette[Math.floor(Math.random() * palette.length)];
}

/* ═══════════════════════════════════════════
   SPAWN PROXIMITY
   New players spawn near the centroid of the
   most recently active players, with jitter.
═══════════════════════════════════════════ */
function computeSpawnPoint() {
  const active = [...players.values()].filter(p => Date.now() - p.lastSeen < 60000);

  if (active.length === 0) {
    // First player — spawn near origin but not exactly on it
    const angle = Math.random() * Math.PI * 2;
    const r = DEAD_ZONE + Math.random() * 200;
    return { x: Math.cos(angle) * r, y: Math.sin(angle) * r };
  }

  // Find centroid of active players
  let cx = 0, cy = 0;
  for (const p of active) { cx += p.x; cy += p.y; }
  cx /= active.length;
  cy /= active.length;

  // Spawn within SPAWN_RADIUS of that centroid, with some jitter so
  // players don't stack exactly
  const angle  = Math.random() * Math.PI * 2;
  const radius = 200 + Math.random() * SPAWN_RADIUS;
  return {
    x: cx + Math.cos(angle) * radius,
    y: cy + Math.sin(angle) * radius,
  };
}

/* ═══════════════════════════════════════════
   SHARED ECONOMY STATE
   Server is authoritative on market prices.
   Clients receive price snapshots each tick.
═══════════════════════════════════════════ */
// Seeded RNG (same algorithm as client)
function xmur3(str) {
  let h = 1779033703 ^ str.length;
  for (let i = 0; i < str.length; i++) {
    h = Math.imul(h ^ str.charCodeAt(i), 3432918353);
    h = (h << 13) | (h >>> 19);
  }
  return () => {
    h = Math.imul(h ^ (h >>> 16), 2246822507);
    h = Math.imul(h ^ (h >>> 13), 3266489909);
    return ((h ^= h >>> 16) >>> 0);
  };
}
function sfc32(a, b, c, d) {
  return () => {
    a|=0;b|=0;c|=0;d|=0;
    let t=(a+b|0)+d|0;d=d+1|0;a=b^b>>>9;
    b=c+(c<<3)|0;c=(c<<21|c>>>11);c=c+t|0;
    return (t>>>0)/4294967296;
  };
}
function makeRng(s) {
  const seed = xmur3(s);
  return sfc32(seed(), seed(), seed(), seed());
}

const RES_KEYS = ["dirt","stone","copper","iron","gold","crystal","fuel",
                  "gas_canister","ice_block","lava_rock","magma_core","toxic_sludge","sand","grass_tuft"];
const RES_BASE = { dirt:1,stone:3,copper:9,iron:10,gold:40,crystal:60,fuel:25,
                   gas_canister:30,ice_block:4,lava_rock:12,magma_core:22,
                   toxic_sludge:8,sand:2,grass_tuft:1 };
const RES_RARITY = { dirt:1,stone:2,copper:3,iron:3,gold:5,crystal:6,fuel:4,
                     gas_canister:2,ice_block:2,lava_rock:3,magma_core:4,
                     toxic_sludge:3,sand:1,grass_tuft:1 };

const economyRng = makeRng(GALAXY_SEED + "|economy");
const economy = {
  drift:    Object.fromEntries(RES_KEYS.map(k => [k, 1])),
  scarcity: Object.fromEntries(RES_KEYS.map(k => [k, 1])),
  tick() {
    for (const k of RES_KEYS) {
      this.drift[k]    = Math.max(0.6, Math.min(1.6, this.drift[k] + (economyRng() - 0.5) * 0.02));
      this.scarcity[k] = this.scarcity[k] + (1 - this.scarcity[k]) * 0.002;
    }
  },
  price(k) {
    const base    = RES_BASE[k] || 1;
    const rarity  = RES_RARITY[k] || 1;
    const f       = 1 + (rarity - 1) * 0.28;
    return Math.max(1, Math.round(base * f * this.drift[k] * this.scarcity[k]));
  },
  sold(k, q)   { this.scarcity[k] = Math.max(0.5, Math.min(1.5, this.scarcity[k] - q * 0.02)); },
  bought(k, q) { this.scarcity[k] = Math.max(0.5, Math.min(1.5, this.scarcity[k] + q * 0.02)); },
  snapshot() {
    const out = {};
    for (const k of RES_KEYS) out[k] = this.price(k);
    return out;
  }
};

/* ═══════════════════════════════════════════
   PVP PROJECTILES  (server-authoritative)
   Clients send "shoot" events; server validates
   and broadcasts to nearby players only.
═══════════════════════════════════════════ */
const pvpProjectiles = [];
const SHOOT_CD   = 0.22;  // seconds between shots
const PROJ_SPEED = 280;
const PROJ_LIFE  = 2.2;
const BASE_DAMAGE = 18;

function tickProjectiles(dt) {
  for (let i = pvpProjectiles.length - 1; i >= 0; i--) {
    const p = pvpProjectiles[i];
    p.x  += p.vx * dt;
    p.y  += p.vy * dt;
    p.life -= dt;
    if (p.life <= 0) { pvpProjectiles.splice(i, 1); continue; }

    // Hit detection against all other players
    for (const [sid, target] of players) {
      if (sid === p.ownerId) continue;
      if (target.mode !== "space") continue;
      if (Math.hypot(p.x - target.x, p.y - target.y) < 12) {
        // Apply damage
        const armor    = 1 + ((target.attrs.armor - 1) * 0.2);
        let dmg        = p.damage / armor;
        if (target.shield > 0) {
          const abs  = Math.min(target.shield, dmg);
          target.shield -= abs;
          dmg -= abs;
        }
        target.hp = Math.max(0, target.hp - dmg);
        target.shieldRegenTimer = 4;

        // Notify victim
        io.to(sid).emit("hit", { damage: Math.round(dmg), hp: target.hp, shield: target.shield, by: p.ownerId });

        // Notify shooter (hit confirmation)
        io.to(p.ownerId).emit("hitConfirm", { targetId: sid, damage: Math.round(dmg) });

        pvpProjectiles.splice(i, 1);

        if (target.hp <= 0) handlePlayerKill(sid, p.ownerId);
        break;
      }
    }
  }
}

function handlePlayerKill(victimId, killerId) {
  const victim = players.get(victimId);
  const killer = players.get(killerId);
  if (!victim) return;

  io.to(victimId).emit("youDied", { killedBy: killer ? killer.name : "Unknown" });
  if (killer) {
    io.to(killerId).emit("killConfirm", { name: victim.name });
    killer.credits += 100;  // bounty
    io.to(killerId).emit("creditUpdate", { credits: killer.credits });
  }

  // Broadcast kill to nearby players
  io.emit("playerKilled", { victimId, victimName: victim.name, killerId, killerName: killer?.name });

  // Respawn victim after 3 seconds
  setTimeout(() => {
    const p = players.get(victimId);
    if (!p) return;
    const spawn = computeSpawnPoint();
    p.x = spawn.x; p.y = spawn.y;
    p.hp = p.maxHp;
    p.shield = p.maxShield;
    p.energy = 100;
    p.shieldRegenTimer = 0;
    io.to(victimId).emit("respawn", { x: p.x, y: p.y });
  }, 3000);
}

/* ═══════════════════════════════════════════
   PHYSICS SIMULATION  (server-side)
   Server simulates each player's ship using
   their last-known input snapshot. This is
   the authoritative position.
═══════════════════════════════════════════ */
const ROT_SPEED  = 2.4;
const BASE_THRUST = 115;
const ENERGY_DRAIN = 1.8;
const ENERGY_IDLE  = 0.15;
const GAS_REFUEL_AMOUNT = 30;

function tickPlayers(dt) {
  for (const [, p] of players) {
    if (p.mode !== "space") continue;

    const speedStat = 1 + ((p.attrs.speed - 1) * 0.3);
    const gasEff    = 1 / Math.max(0.3, 1 + ((p.attrs.gasEfficiency - 1) * 0.15));
    const shRegen   = 3 * (1 + ((p.attrs.shieldRegen - 1) * 0.4));
    const inp       = p.input;

    if (inp.rotLeft)  p.angle -= ROT_SPEED * dt;
    if (inp.rotRight) p.angle += ROT_SPEED * dt;

    const thrust = BASE_THRUST * speedStat;
    if (inp.thrust) {
      p.vx += Math.cos(p.angle) * thrust * dt;
      p.vy += Math.sin(p.angle) * thrust * dt;
      p.energy = Math.max(0, p.energy - ENERGY_DRAIN * gasEff * dt);
    } else if (Math.hypot(p.vx, p.vy) > 5) {
      p.energy = Math.max(0, p.energy - ENERGY_IDLE * gasEff * dt);
    }

    if (inp.brake) { p.vx *= 0.92; p.vy *= 0.92; }

    const drag = Math.pow(0.995, dt * 60);
    p.vx *= drag; p.vy *= drag;
    p.x  += p.vx * dt;
    p.y  += p.vy * dt;

    // Shield regen
    p.shieldRegenTimer = Math.max(0, p.shieldRegenTimer - dt);
    if (p.shieldRegenTimer <= 0 && p.shield < p.maxShield) {
      p.shield = Math.min(p.maxShield, p.shield + shRegen * dt);
    }

    // Shoot cooldown
    if (inp.shootX !== null && p.shootCooldown <= 0 && p.hp > 0) {
      const ang = Math.atan2(inp.shootY - p.y, inp.shootX - p.x);
      const damageStat = 1 + ((p.attrs.damage - 1) * 0.4);
      pvpProjectiles.push({
        id: `${p.id}_${Date.now()}_${Math.random()}`,
        ownerId: p.id,
        ownerName: p.name,
        x: p.x, y: p.y,
        vx: Math.cos(ang) * PROJ_SPEED,
        vy: Math.sin(ang) * PROJ_SPEED,
        damage: BASE_DAMAGE * damageStat,
        life: PROJ_LIFE,
      });
      p.shootCooldown = SHOOT_CD;
      inp.shootX = null; inp.shootY = null;  // consume
    }
    if (p.shootCooldown > 0) p.shootCooldown = Math.max(0, p.shootCooldown - dt);

    p.lastSeen = Date.now();
  }
}

/* ═══════════════════════════════════════════
   BROADCAST  (spatial partitioning)
   Each player only receives state for players
   within BROADCAST_RANGE to save bandwidth.
═══════════════════════════════════════════ */
function buildPlayerSnapshot(p) {
  return {
    id:     p.id,
    name:   p.name,
    x:      p.x,
    y:      p.y,
    vx:     p.vx,
    vy:     p.vy,
    angle:  p.angle,
    hp:     p.hp,
    maxHp:  p.maxHp,
    shield: p.shield,
    maxShield: p.maxShield,
    color:  p.color,
    level:  p.level,
    mode:   p.mode,
  };
}

function broadcastWorldState() {
  const allSnapshots = [...players.values()].map(buildPlayerSnapshot);
  const projSnapshots = pvpProjectiles.map(p => ({
    id: p.id, x: p.x, y: p.y, vx: p.vx, vy: p.vy, ownerId: p.ownerId
  }));

  for (const [sid, p] of players) {
    // Filter other players to nearby only
    const nearby = allSnapshots.filter(s => {
      if (s.id === sid) return false;
      return Math.hypot(s.x - p.x, s.y - p.y) < BROADCAST_RANGE;
    });

    // Filter projectiles near this player
    const nearbyProj = projSnapshots.filter(pr =>
      Math.hypot(pr.x - p.x, pr.y - p.y) < BROADCAST_RANGE
    );

    io.to(sid).emit("worldState", {
      self: buildPlayerSnapshot(p),
      others: nearby,
      pvpProjectiles: nearbyProj,
    });
  }
}

/* ═══════════════════════════════════════════
   ECONOMY BROADCAST  (every 5s)
═══════════════════════════════════════════ */
let economyBroadcastTimer = 0;
function broadcastEconomy() {
  io.emit("economyUpdate", economy.snapshot());
}

/* ═══════════════════════════════════════════
   CHAT
═══════════════════════════════════════════ */
function broadcastChat(from, message) {
  const safe = String(message).replace(/</g,"&lt;").slice(0, 120);
  io.emit("chat", { from, message: safe, ts: Date.now() });
}

/* ═══════════════════════════════════════════
   MAIN TICK LOOP
═══════════════════════════════════════════ */
let lastTick = Date.now();
setInterval(() => {
  const now = Date.now();
  const dt  = Math.min((now - lastTick) / 1000, 0.05);
  lastTick  = now;

  economy.tick();
  tickPlayers(dt);
  tickProjectiles(dt);
  broadcastWorldState();

  economyBroadcastTimer += dt;
  if (economyBroadcastTimer >= 5) {
    broadcastEconomy();
    economyBroadcastTimer = 0;
  }
}, TICK_MS);

/* ═══════════════════════════════════════════
   SOCKET EVENTS
═══════════════════════════════════════════ */
io.on("connection", socket => {
  if (players.size >= MAX_PLAYERS) {
    socket.emit("serverFull");
    socket.disconnect(true);
    return;
  }

  console.log(`[+] ${socket.id} connected (${players.size + 1} total)`);

  // ── Join ──
  socket.on("join", ({ name }) => {
    if (players.has(socket.id)) return; // already joined

    const spawn = computeSpawnPoint();
    const p     = defaultPlayer(socket.id, name, spawn.x, spawn.y);
    players.set(socket.id, p);

    // Send this player their initial state + the galaxy seed so client
    // can generate the exact same procedural world
    socket.emit("welcome", {
      id:          socket.id,
      x:           p.x,
      y:           p.y,
      color:       p.color,
      galaxySeed:  GALAXY_SEED,
      prices:      economy.snapshot(),
      playerCount: players.size,
    });

    // Announce to others
    socket.broadcast.emit("playerJoined", { id: p.id, name: p.name, color: p.color });
    broadcastChat("Server", `${p.name} has entered the galaxy.`);

    console.log(`  Spawned ${p.name} at (${Math.round(p.x)}, ${Math.round(p.y)})`);
  });

  // ── Input ──
  // Client sends its input state each frame; server applies it on next tick
  socket.on("input", ({ rotLeft, rotRight, thrust, brake, shootX, shootY }) => {
    const p = players.get(socket.id);
    if (!p) return;
    p.input.rotLeft  = !!rotLeft;
    p.input.rotRight = !!rotRight;
    p.input.thrust   = !!thrust;
    p.input.brake    = !!brake;
    // Only queue a shot if none pending
    if (shootX !== undefined && p.input.shootX === null) {
      p.input.shootX = shootX;
      p.input.shootY = shootY;
    }
  });

  // ── Mode change (land/takeoff) ──
  socket.on("modeChange", ({ mode, planetId, x, y }) => {
    const p = players.get(socket.id);
    if (!p) return;
    p.mode     = mode;
    p.planetId = planetId || null;
    if (x !== undefined) { p.x = x; p.y = y; }
  });

  // ── Economy: sell ──
  socket.on("sell", ({ resourceType, quantity, stationId }) => {
    const p = players.get(socket.id);
    if (!p || quantity <= 0 || quantity > 500) return;
    const price = economy.price(resourceType);
    if (!price) return;
    const earned = price * quantity;
    p.credits += earned;
    economy.sold(resourceType, quantity);
    socket.emit("sellConfirm", { resourceType, quantity, earned, credits: p.credits, prices: economy.snapshot() });
    console.log(`  ${p.name} sold ${quantity}x ${resourceType} for ${earned}cr`);
  });

  // ── Economy: buy ──
  socket.on("buy", ({ resourceType, quantity, pricePerUnit }) => {
    const p = players.get(socket.id);
    if (!p || quantity <= 0 || quantity > 500) return;
    const serverPrice = economy.price(resourceType);
    // Accept if client price is within 20% of server price (lag tolerance)
    if (Math.abs(pricePerUnit - serverPrice) / serverPrice > 0.2) {
      socket.emit("buyDenied", { reason: "Price has changed. Please retry." });
      return;
    }
    const cost = serverPrice * quantity;
    if (p.credits < cost) { socket.emit("buyDenied", { reason: "Insufficient credits." }); return; }
    p.credits -= cost;
    economy.bought(resourceType, quantity);
    socket.emit("buyConfirm", { resourceType, quantity, cost, credits: p.credits, prices: economy.snapshot() });
  });

  // ── Gas canister use ──
  socket.on("useGas", () => {
    const p = players.get(socket.id);
    if (!p) return;
    p.energy = Math.min(100, p.energy + GAS_REFUEL_AMOUNT);
    socket.emit("energyUpdate", { energy: p.energy });
  });

  // ── Attribute upgrade ──
  socket.on("upgradeAttr", ({ attr }) => {
    const p = players.get(socket.id);
    if (!p) return;
    const validAttrs = ["damage","speed","cargoMax","armor","gasEfficiency","shieldRegen"];
    if (!validAttrs.includes(attr)) return;
    if ((p.attrPoints || 0) <= 0) { socket.emit("upgradeDenied", { reason: "No attribute points." }); return; }
    if ((p.attrs[attr] || 1) >= 10) { socket.emit("upgradeDenied", { reason: "Already maxed." }); return; }
    p.attrs[attr] = (p.attrs[attr] || 1) + 1;
    p.attrPoints  = (p.attrPoints || 0) - 1;
    socket.emit("attrConfirm", { attr, val: p.attrs[attr], attrPoints: p.attrPoints });
  });

  // ── XP grant (client reports mining/kill XP; server validates roughly) ──
  socket.on("gainXp", ({ amount }) => {
    const p = players.get(socket.id);
    if (!p || amount <= 0 || amount > 500) return;
    p.xp = (p.xp || 0) + amount;
    const xpToNext = Math.floor(100 * Math.pow(1.4, p.level - 1));
    if (p.xp >= xpToNext) {
      p.xp -= xpToNext;
      p.level++;
      p.attrPoints = (p.attrPoints || 0) + 2;
      socket.emit("levelUp", { level: p.level, attrPoints: p.attrPoints });
    }
    socket.emit("xpUpdate", { xp: p.xp, level: p.level });
  });

  // ── Chat ──
  socket.on("chat", ({ message }) => {
    const p = players.get(socket.id);
    if (!p) return;
    broadcastChat(p.name, message);
  });

  // ── Ping / latency ──
  socket.on("ping", (cb) => { if (typeof cb === "function") cb(); });

  // ── Disconnect ──
  socket.on("disconnect", () => {
    const p = players.get(socket.id);
    if (p) {
      console.log(`[-] ${p.name} disconnected (${players.size - 1} remaining)`);
      broadcastChat("Server", `${p.name} has left the galaxy.`);
      socket.broadcast.emit("playerLeft", { id: socket.id });
    }
    players.delete(socket.id);
  });
});

/* ═══════════════════════════════════════════
   START
═══════════════════════════════════════════ */
const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`🚀 Space Eco server running on port ${PORT}`);
  console.log(`   Tick rate : ${TICK_RATE}Hz`);
  console.log(`   Max players: ${MAX_PLAYERS}`);
});
