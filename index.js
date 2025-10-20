// index.js
require("dotenv").config();
const fs = require("fs");
const axios = require("axios");
const cheerio = require("cheerio");
const WebSocket = require('ws');
const {
  Client,
  GatewayIntentBits,
  Partials,
  ActionRowBuilder,
  ButtonBuilder,
  ButtonStyle,
  EmbedBuilder,
  StringSelectMenuBuilder, 
  StringSelectMenuOptionBuilder,
} = require("discord.js");

const client = new Client({
  intents: [
    GatewayIntentBits.Guilds,
    GatewayIntentBits.GuildMessages,
    GatewayIntentBits.MessageContent,
    GatewayIntentBits.GuildVoiceStates, // <-- required for voiceStateUpdate
  ],
  partials: [Partials.Message, Partials.Channel, Partials.Reaction],
});

// ---------------- MONGODB SETUP ----------------
const { MongoClient } = require('mongodb');

let db, playerDataCollection, matchHistoryCollection;

async function connectDB() {
    try {
        console.log('🔗 Connecting to MongoDB...');
        const client = new MongoClient(process.env.MONGODB_URI);
        await client.connect();
        db = client.db('discord-bot');
        playerDataCollection = db.collection('playerData');
        matchHistoryCollection = db.collection('matchHistory');
        console.log('✅ Connected to MongoDB successfully!');
    } catch (error) {
        console.error('❌ MongoDB connection failed:', error);
        console.log('⚠️  Falling back to local file storage');
    }
}

// ---------------- CONFIG ----------------
const DATA_FILE = "playerData.json";
const QUEUE_SIZE = 10;
const MATCH_HISTORY_FILE = "matchHistory.json";

let queue = [];
let matches = new Map();
let queueMessage;
let leaderboardMessage;
let activeReadyCheck = null;
let queueEnabled = true;
let bannedUsers = new Set();
let requestCount = 0;
let saveDataTimeout = null;

// Add block system
let userBlocks = new Map(); // userId -> Set of blocked user IDs

// ADD SOLUTION 1: Queue Locking
let queueLock = false;

// Message Delete Queue
class MessageDeleteQueue {
    constructor() {
        this.queue = [];
        this.isProcessing = false;
        this.delayBetweenDeletes = 2000; // 2 second between deletions
    }

    addMessage(message) {
        this.queue.push(message);
        if (!this.isProcessing) {
            this.processQueue();
        }
    }

    async processQueue() {
        this.isProcessing = true;
        while (this.queue.length > 0) {
            const message = this.queue.shift();
            try {
                await message.delete();
                console.log('✅ Deleted message from queue channel');
            } catch (error) {
                if (error.code === 10008) { // Unknown Message (already deleted)
                    console.log('ℹ️ Message already deleted');
                } else {
                    console.error('Error deleting message:', error);
                }
            }
            // Wait before processing the next message
            await new Promise(resolve => setTimeout(resolve, this.delayBetweenDeletes));
        }
        this.isProcessing = false;
    }
}

// Initialize the delete queue
const deleteQueue = new MessageDeleteQueue();

const TIMEOUT_LEVELS = [
  1 * 60 * 1000,      // 1 minute
  5 * 60 * 1000,      // 5 minutes  
  25 * 60 * 1000,     // 25 minutes
  60 * 60 * 1000,     // 1 hour
  24 * 60 * 60 * 1000 // 24 hours
];
const WEEKLY_RESET_MS = 7 * 24 * 60 * 60 * 1000; // 1 week in milliseconds

// ---------------- WEEKLY RESET FUNCTION ----------------
function checkWeeklyReset(timeoutTracking) {
  const now = Date.now();
  
  // If weekly reset time has passed, reset all player timeouts
  if (now >= timeoutTracking.weeklyReset) {
    console.log("🔄 Performing weekly timeout reset");
    
    // Reset all player offenses
    timeoutTracking.playerTimeouts = {};
    
    // Set next weekly reset (1 week from now)
    timeoutTracking.weeklyReset = now + WEEKLY_RESET_MS;
    
    // Save the updated data
    saveData();
  }
}

let playerData = loadData();

function ensurePlayer(id) {
  if (!playerData[id]) {
    playerData[id] = { 
      rank: "Iron", 
      division: 4, 
      lp: 0, 
      wins: 0, 
      losses: 0,
      roles: [] // Make sure roles array is initialized
    };
  }
  
  // Ensure all required properties exist
  const player = playerData[id];
  if (player.rank === undefined) player.rank = "Iron";
  if (player.division === undefined) player.division = 4;
  if (player.lp === undefined) player.lp = 0;
  if (player.wins === undefined) player.wins = 0;
  if (player.losses === undefined) player.losses = 0;
  if (player.roles === undefined) player.roles = [];
  
  return playerData[id];
}

function getNextMatchId() {
  const matchHistory = loadMatchHistory();
  
  // If no matches exist, start from 1
  if (matchHistory.length === 0) {
    return "1";
  }
  
  // Extract all numeric IDs and find the maximum
  const numericIds = matchHistory
    .map(match => {
      // Convert string IDs to numbers, ignore non-numeric
      const id = match.id;
      if (typeof id === 'number') return id;
      if (typeof id === 'string') {
        const num = parseInt(id);
        return isNaN(num) ? 0 : num;
      }
      return 0;
    })
    .filter(id => id > 0); // Only positive numbers
  
  // If we found valid numeric IDs, use the max + 1
  if (numericIds.length > 0) {
    const maxId = Math.max(...numericIds);
    return (maxId + 1).toString();
  }
  
  // Fallback: start from current count + 1
  return (matchHistory.length + 1).toString();
}

// Add this function to load/save match history
async function loadMatchHistory() {
    if (matchHistoryCollection) {
        try {
            const history = await matchHistoryCollection.find({}).sort({ timestamp: 1 }).toArray();
            console.log(`📥 Loaded ${history.length} matches from MongoDB`);
            return history;
        } catch (error) {
            console.error('Error loading match history from MongoDB:', error);
        }
    }
    
    // Fallback to file
    if (fs.existsSync(MATCH_HISTORY_FILE)) {
        return JSON.parse(fs.readFileSync(MATCH_HISTORY_FILE));
    }
    return [];
}

async function saveMatchHistory(history) {
    if (matchHistoryCollection) {
        try {
            // Clear and rebuild collection
            await matchHistoryCollection.deleteMany({});
            if (history.length > 0) {
                await matchHistoryCollection.insertMany(history);
            }
            console.log(`💾 Saved ${history.length} matches to MongoDB`);
            return;
        } catch (error) {
            console.error('Error saving match history to MongoDB:', error);
        }
    }
    
    // Fallback to file
    fs.writeFileSync(MATCH_HISTORY_FILE, JSON.stringify(history, null, 2));
}

// ---------------- RANK SYSTEM ----------------
const ranks = ["Iron", "Bronze", "Silver", "Gold", "Platinum", "Emerald", "Diamond"];
function getIHP(player) {
  if (["Master", "Grandmaster", "Challenger"].includes(player.rank)) {
    return 2800 + player.lp;
  }
  const tierIndex = ranks.indexOf(player.rank);
  if (tierIndex < 0) return 0;
  let divisionValue = 0;
  if (player.division) {
    divisionValue = (5 - player.division) * 100 - 100;
  }
  return tierIndex * 400 + divisionValue + player.lp;
}
function IHPToRank(IHP) {
  // Prevent going below the lowest possible value (Iron IV 0 LP)
  if (IHP <= 0) {
    return { rank: "Iron", division: 4, lp: 0 };
  }

  if (IHP >= 2800) {
    // Master+
    const lp = IHP - 2800;
    if (lp >= 900) return { rank: "Challenger", division: null, lp };
    if (lp >= 500) return { rank: "Grandmaster", division: null, lp };
    return { rank: "Master", division: null, lp };
  }

  const tierIndex = Math.floor(IHP / 400);
  const tier = ranks[tierIndex] || "Iron"; // default to Iron if somehow undefined
  let remainingIHP = IHP - tierIndex * 400;
  let division = 4;
  let lp = remainingIHP;

  while (lp >= 100 && division > 1) {
    lp -= 100;
    division--;
  }

  // Safety: if anything goes negative, reset to base Iron IV 0 LP
  if (lp < 0) lp = 0;

  return { rank: tier, division, lp };
}

// ---------------- DATA FUNCTIONS ----------------
async function loadData() {
    // If MongoDB is connected, use it
    if (playerDataCollection) {
        try {
            const data = await playerDataCollection.findOne({ _id: 'main' });
            if (data) {
                console.log('📥 Loaded data from MongoDB');
                
                // Convert arrays back to Sets
                if (data._bannedUsers) bannedUsers = new Set(data._bannedUsers);
                if (data._userBlocks) {
                    userBlocks = new Map(Object.entries(data._userBlocks).map(([k, v]) => [k, new Set(v)]));
                }
                
                return data;
            }
        } catch (error) {
            console.error('Error loading from MongoDB:', error);
        }
    }
    
    // Fallback to file system
    if (fs.existsSync(DATA_FILE)) {
        console.log('📥 Loaded data from local file');
        const data = JSON.parse(fs.readFileSync(DATA_FILE));
        bannedUsers = new Set(data._bannedUsers || []);
        return data;
    }
    
    console.log('🆕 Starting with fresh data');
    return {
        _timeoutTracking: {
            weeklyReset: Date.now() + WEEKLY_RESET_MS,
            playerTimeouts: {}
        },
        _smurfRefunds: {
            processedMatches: new Set(),
            processedSmurfs: new Set(),
            refundHistory: {}
        }
    };
}

async function saveData() {
    // Debounce save operations
    if (saveDataTimeout) {
        clearTimeout(saveDataTimeout);
    }

    saveDataTimeout = setTimeout(async () => {
        const dataToSave = { 
            ...playerData, 
            _bannedUsers: Array.from(bannedUsers),
            _timeoutTracking: playerData._timeoutTracking,
            _userBlocks: Object.fromEntries(Array.from(userBlocks.entries()).map(([k, v]) => [k, Array.from(v)])),
            _smurfRefunds: {
                processedMatches: Array.from(playerData._smurfRefunds?.processedMatches || new Set()),
                processedSmurfs: Array.from(playerData._smurfRefunds?.processedSmurfs || new Set()),
                refundHistory: playerData._smurfRefunds?.refundHistory || {}
            }
        };

        // Try MongoDB first
        if (playerDataCollection) {
            try {
                await playerDataCollection.updateOne(
                    { _id: 'main' },
                    { $set: dataToSave },
                    { upsert: true }
                );
                console.log('💾 Saved to MongoDB');
                return;
            } catch (error) {
                console.error('Error saving to MongoDB:', error);
            }
        }
        
        // Fallback to file
        fs.writeFileSync(DATA_FILE, JSON.stringify(dataToSave, null, 2));
        console.log('💾 Saved to local file');
    }, 1000);
}

setInterval(() => { requestCount = 0; }, 1000); // Reset every second
// Wrap your API calls
function trackRequest() {
    requestCount++;
    if (requestCount > 40) { // Leave buffer below 50
        console.warn(`⚠️ Approaching global limit: ${requestCount}/50 requests this second`);
    }
}

// ---------------- Role Selection -------------
const ROLES = [
  { label: "Fill", value: "Fill" },
  { label: "Top", value: "Top" },
  { label: "Jungle", value: "Jungle" },
  { label: "Mid", value: "Mid" },
  { label: "Bot", value: "Bot" },
  { label: "Support", value: "Support" }
];



// ---------------- BLOCK SYSTEM ----------------
function getUserBlocks(userId) {
  if (!userBlocks.has(userId)) {
    userBlocks.set(userId, new Set());
  }
  return userBlocks.get(userId);
}

function addBlock(blockerId, blockedId) {
  const blocks = getUserBlocks(blockerId);
  blocks.add(blockedId);
  saveData();
  return blocks;
}

function removeBlock(blockerId, blockedId) {
  const blocks = getUserBlocks(blockerId);
  blocks.delete(blockedId);
  saveData();
  return blocks;
}

function getBlockedUsers(blockerId) {
  return Array.from(getUserBlocks(blockerId));
}

function hasBlockConflict(user1, user2) {
  return getUserBlocks(user1).has(user2) || getUserBlocks(user2).has(user1);
}

function checkQueueForBlocks(userId) {
  const userBlocks = getUserBlocks(userId);
  const blockedInQueue = queue.filter(queuedUser => userBlocks.has(queuedUser));
  return blockedInQueue;
}

// ---------------- TIMEOUT SYSTEM ----------------
function getPlayerTimeout(userId) {
  if (!playerData._timeoutTracking.playerTimeouts[userId]) {
    playerData._timeoutTracking.playerTimeouts[userId] = {
      offenses: 0,
      timeoutUntil: 0
    };
  }
  return playerData._timeoutTracking.playerTimeouts[userId];
}

function addTimeoutOffense(userId) {
  const playerTimeout = getPlayerTimeout(userId);
  playerTimeout.offenses = Math.min(playerTimeout.offenses + 1, TIMEOUT_LEVELS.length);
  
  const timeoutDuration = TIMEOUT_LEVELS[playerTimeout.offenses - 1] || TIMEOUT_LEVELS[TIMEOUT_LEVELS.length - 1];
  playerTimeout.timeoutUntil = Date.now() + timeoutDuration;
  
  console.log(`⏰ Timeout offense for ${userId}: level ${playerTimeout.offenses}, duration: ${timeoutDuration/1000/60} minutes`);
  saveData();
  
  return playerTimeout;
}

function isUserInTimeout(userId) {
  const playerTimeout = getPlayerTimeout(userId);
  const now = Date.now();
  
  if (now < playerTimeout.timeoutUntil) {
    return {
      inTimeout: true,
      timeLeft: playerTimeout.timeoutUntil - now,
      offenses: playerTimeout.offenses
    };
  }
  
  return { inTimeout: false, timeLeft: 0, offenses: playerTimeout.offenses };
}

// ---------------- DISCORD TIMESTAMPS ----------------
function createDiscordTimestamp(targetTime, style = 'R') {
  // targetTime can be a Date object or milliseconds
  const timestamp = Math.floor(new Date(targetTime).getTime() / 1000);
  return `<t:${timestamp}:${style}>`;
}

// ---------------- HELPER FUNCTIONS ----------------
function formatRankDisplay(rank, division, lp) {
  if (division) {
    return `${rank} ${division} ${lp}LP`;
  }
  return `${rank} ${lp}LP`;
}

function formatTimeLeft(ms) {
  if (ms >= 24 * 60 * 60 * 1000) {
    return `${Math.ceil(ms / (24 * 60 * 60 * 1000))} days`;
  } else if (ms >= 60 * 60 * 1000) {
    return `${Math.ceil(ms / (60 * 60 * 1000))} hours`;
  } else if (ms >= 60 * 1000) {
    return `${Math.ceil(ms / (60 * 1000))} minutes`;
  } else {
    return `${Math.ceil(ms / 1000)} seconds`;
  }
}

function getTimeoutInfo(userId) {
  const playerTimeout = getPlayerTimeout(userId);
  const timeoutStatus = isUserInTimeout(userId);
  
  return {
    offenses: playerTimeout.offenses,
    inTimeout: timeoutStatus.inTimeout,
    timeLeft: timeoutStatus.timeLeft,
    nextTimeout: playerTimeout.offenses < TIMEOUT_LEVELS.length ? 
      TIMEOUT_LEVELS[playerTimeout.offenses] : TIMEOUT_LEVELS[TIMEOUT_LEVELS.length - 1]
  };
}

// ---------------- LEADERBOARD ----------------
async function updateLeaderboardChannel(guild) {
  const channelName = "leaderboard";
  let lbChannel = guild.channels.cache.find(c => c.name === channelName && c.type === 0);
  if (!lbChannel) {
    lbChannel = await guild.channels.create({ name: channelName, type: 0 });
  }

  // Try to reuse old leaderboard messages
  if (!leaderboardMessage || !leaderboardMessage.length) {
    const fetched = await lbChannel.messages.fetch({ limit: 20 });
    const existing = fetched.filter(m => m.author.id === client.user.id && m.embeds.length > 0);
    if (existing.size > 0) {
      leaderboardMessage = Array.from(existing.values()).sort((a, b) => a.createdTimestamp - b.createdTimestamp);
      console.log(`Found ${leaderboardMessage.length} existing leaderboard messages.`);
    } else {
      leaderboardMessage = [];
    }
  }

  // Build leaderboard sorted by Elo/IHP
  const players = Object.keys(playerData)
    .map(id => {
      const p = playerData[id];
      const gp = p.wins + p.losses;
      const wr = gp ? ((p.wins / gp) * 100).toFixed(1) : "0.0";
      return {
        id,
        rank: p.rank,
        division: p.division,
        lp: p.lp,
        elo: getIHP(p),
        wins: p.wins,
        losses: p.losses,
        wr,
        gp
      };
    })
    .sort((a, b) => b.elo - a.elo); // highest Elo first

  // Split into chunks of 25
  const chunkSize = 25;
  const embeds = [];
  for (let i = 0; i < players.length; i += chunkSize) {
    const chunk = players.slice(i, i + chunkSize);
    const description = chunk
      .map((p, idx) => {
        const rankDiv = p.division ? `${p.rank} ${p.division}` : p.rank;
        const lpLabel = "LP";
        const line1 = `#${i + idx + 1} • ${rankDiv} ${p.lp} LP`;
        const line2 = `<@${p.id}> | Elo: ${p.elo} | W: ${p.wins} | L: ${p.losses} | WR: ${p.wr}% | GP: ${p.gp}`;
        return `${line1}\n${line2}`;
      })
      .join("\n\n");

    const embed = new EmbedBuilder()
      .setTitle(i === 0 ? "🏆 Leaderboard" : `Leaderboard (cont.)`)
      .setDescription(description)
      .setColor(0xffd700)
      .setTimestamp();
    embeds.push(embed);
  }

  // EDIT existing messages if they exist
  if (leaderboardMessage && leaderboardMessage.length) {
    for (let i = 0; i < embeds.length; i++) {
      const embed = embeds[i];
      if (leaderboardMessage[i]) {
        // Edit existing message
        await leaderboardMessage[i].edit({ embeds: [embed] }).catch(() => {});
      } else {
        // Add new message if needed
        const msg = await lbChannel.send({ embeds: [embed] });
        leaderboardMessage.push(msg);
      }
    }
    // Delete any extra old messages
    if (leaderboardMessage.length > embeds.length) {
      for (let i = embeds.length; i < leaderboardMessage.length; i++) {
        await leaderboardMessage[i].delete().catch(() => {});
      }
      leaderboardMessage = leaderboardMessage.slice(0, embeds.length);
    }
  } else {
    // No previous messages → send new ones
    leaderboardMessage = [];
    for (const embed of embeds) {
      const msg = await lbChannel.send({ embeds: [embed] });
      leaderboardMessage.push(msg);
    }
  }
}

// ---------------- READY CHECK ----------------
async function startReadyCheck(channel) {
  // Safety Check in startReadyCheck
  if (queue.length !== QUEUE_SIZE) {
    console.warn(`⚠️ Ready check attempted with ${queue.length} players, expected ${QUEUE_SIZE}`);
    return;
  }
  
  if (activeReadyCheck) {
    console.warn("⚠️ Ready check already active, ignoring duplicate");
    return;
  }

  const participants = [...queue];
  const ready = new Set();
  const declined = new Set();
  const TIMEOUT = 60; // 60 seconds
  const endTime = Date.now() + (TIMEOUT * 1000);

  // Debounce variables
  let pendingUpdate = false;
  let updateTimeout = null;
  const DEBOUNCE_DELAY = 300; // 300ms debounce

  // Create the initial embed with Discord timestamp - REMOVED FOOTER
  const createReadyCheckEmbed = () => {
    const readyArray = Array.from(ready);
    const waitingArray = participants.filter(id => !ready.has(id) && !declined.has(id));
    const declinedArray = Array.from(declined);
    
    const embed = new EmbedBuilder()
      .setTitle("⚔️ Ready Check")
      .setDescription(
        `${participants.length} players have queued!\n\n` +
        `**Click ✅ Ready if you're ready**\n` +
        `**Click ❌ Decline if you can't**\n\n` +
        `⏳ **Time remaining:** ${createDiscordTimestamp(endTime, 'R')}\n\n` +
        `**Ready (${ready.size}/${participants.length}):**\n` +
        `${readyArray.length > 0 ? readyArray.map(id => `<@${id}> ✅`).join('\n') : 'None yet'}\n\n` +
        `**Waiting for response:**\n` +
        `${waitingArray.length > 0 ? waitingArray.map(id => `<@${id}> ⏳`).join('\n') : 'None'}`
      )
      .setColor(0x00ffff);

    if (declinedArray.length > 0) {
      embed.addFields({
        name: "❌ Declined",
        value: declinedArray.map(id => `<@${id}>`).join('\n'),
      });
    }

    return embed;
  };

  // Debounced update function
  const debouncedUpdate = async () => {
    if (updateTimeout) {
      clearTimeout(updateTimeout);
    }
    
    updateTimeout = setTimeout(async () => {
      try {
        const updatedEmbed = createReadyCheckEmbed();
        await msg.edit({ embeds: [updatedEmbed] }).catch(() => {});
        pendingUpdate = false;
      } catch (error) {
        console.log('Edit error during ready check:', error.message);
        pendingUpdate = false;
      }
    }, DEBOUNCE_DELAY);
  };

  // Cache the row components to avoid rebuilding them every second
  const row = new ActionRowBuilder().addComponents(
    new ButtonBuilder()
      .setCustomId("ready")
      .setLabel("✅ Ready")
      .setStyle(ButtonStyle.Success),
    new ButtonBuilder()
      .setCustomId("notready")
      .setLabel("❌ Decline")
      .setStyle(ButtonStyle.Danger)
  );

  // Send initial message
  const msg = await channel.send({
    content: participants.map((id) => `<@${id}>`).join(" "),
    embeds: [createReadyCheckEmbed()],
    components: [row],
  });

  // Create collector
  const collector = msg.createMessageComponentCollector({ time: TIMEOUT * 1000 });

  // Register active ready-check so !forceready can stop it
  activeReadyCheck = { msg, collector };

  collector.on("collect", async (i) => {
    if (!participants.includes(i.user.id)) {
        return i.reply({ content: "You're not in this queue.", ephemeral: true });
    }

    if (i.customId === "notready") {
        console.log("Decline button clicked by:", i.user.id);
        // Apply timeout punishment for declining
        const timeoutInfo = addTimeoutOffense(i.user.id);
        const timeoutStatus = isUserInTimeout(i.user.id);
        const timeLeft = formatTimeLeft(timeoutStatus.timeLeft);
        
        // Remove player from queue
        queue = queue.filter((id) => id !== i.user.id);
        declined.add(i.user.id);
        saveData();
        await updateQueueMessage();

        await i.reply({
            content: `❌ You have declined the queue and received a timeout penalty. You cannot queue for ${timeLeft}.`,
            ephemeral: true,
        });
        
        // Send notification about the timeout
        await msg.channel.send({
            content: `⚠️ <@${i.user.id}> declined the ready check and received a timeout penalty (${timeoutInfo.offenses} offense${timeoutInfo.offenses > 1 ? 's' : ''}) - cannot queue for ${timeLeft}`
        });
        
        collector.stop("declined");
        return;
    }

    // Prevent multiple ready clicks from same user
    if (ready.has(i.user.id)) {
        // Silently ignore - user already ready
        await i.deferUpdate().catch(() => {});
        return;
    }

    // Mark ready
    ready.add(i.user.id);
    
    // ✅ DEBOUNCED UPDATE - Batch rapid clicks
    debouncedUpdate();

    await i.deferUpdate().catch((err) => {
      if (err.code !== 10062) console.error("Button deferUpdate error:", err);
    });

    if (ready.size === participants.length) {
      // If all players are ready, update immediately (no debounce)
      if (updateTimeout) {
        clearTimeout(updateTimeout);
      }
      try {
        const updatedEmbed = createReadyCheckEmbed();
        await msg.edit({ embeds: [updatedEmbed] }).catch(() => {});
      } catch (error) {
        console.log('Edit error during ready check:', error.message);
      }
      collector.stop("all_ready");
    }
    return;
  });
  
  collector.on("end", async (_, reason) => {
    // Clean up debounce timer
    if (updateTimeout) {
      clearTimeout(updateTimeout);
    }
    activeReadyCheck = null;

    let description = "";
    if (reason === "all_ready") {
        description = "✅ All players ready. Match is starting!";
    } else if (reason === "declined") {
        description = "❌ A player declined the ready check and received a timeout penalty. Match canceled.";
    } else {
        // ✅ TIMEOUT REASON - APPLY PENALTIES TO PLAYERS WHO DIDN'T RESPOND
        description = "⌛ Ready check timed out. Match canceled.";
        
        const notReady = participants.filter((id) => !ready.has(id) && !declined.has(id));
        if (notReady.length > 0) {
            queue = queue.filter((id) => !notReady.includes(id));
            saveData();
            await updateQueueMessage();
            
            // Apply timeout offenses to players who didn't respond
            const timeoutMessages = [];
            for (const userId of notReady) {
                const timeoutInfo = addTimeoutOffense(userId);
                const timeoutStatus = isUserInTimeout(userId);
                const timeLeft = formatTimeLeft(timeoutStatus.timeLeft);
                
                timeoutMessages.push(`<@${userId}> - ${timeoutInfo.offenses} offense(s) - banned for ${timeLeft}`);
            }
            
            await msg.channel.send({
                content: `⌛ Ready check timed out. The following players did not respond and received timeout penalties:\n${timeoutMessages.join("\n")}`
            });
        }
    }

    const finalEmbed = EmbedBuilder.from(createReadyCheckEmbed())
        .setDescription(description)
        .setColor(
            reason === "all_ready"
                ? 0x00ff00
                : reason === "declined"
                ? 0xff0000
                : 0xffa500
        );

    await msg.edit({ embeds: [finalEmbed], components: [] }).catch(() => {});

    // ✅ Schedule deletion for 50 seconds later
    setTimeout(async () => {
      try {
        // Check if message is still deletable before attempting
        const freshMessage = await msg.channel.messages.fetch(msg.id).catch(() => null);
        if (freshMessage && freshMessage.deletable) {
          await freshMessage.delete();
          console.log('✅ Ready check embed deleted after completion');
        }
      } catch (error) {
        if (error.code !== 10008) { // Unknown Message (already deleted)
          console.error('Error deleting ready check embed:', error);
        }
      }
    }, 50000); // 50 seconds

    if (reason === "all_ready") {
        await makeTeams(channel);
    } else {
        await updateQueueMessage();
    }
  });
}

// Post role selection in #how-to-play
async function postRoleSelectionMessage(channel) {
  const buttonRow = new ActionRowBuilder().addComponents(
    new ButtonBuilder()
      .setCustomId('open_role_selection')
      .setLabel('🎮 Set Roles')
      .setStyle(ButtonStyle.Primary)
  );

  const embed = new EmbedBuilder()
    .setTitle("🎮 Set Your Role Preferences")
    .setDescription("**Click below to set your 5 preferred roles**\n\n1️⃣ = Most preferred\n5️⃣ = Least preferred\n\n*Select 'Fill' for any position - all subsequent roles will auto-fill*")
    .setColor(0x0099FF);

  // Check if message already exists
  const existing = (await channel.messages.fetch({ limit: 10 }))
    .filter(m => m.author.id === client.user.id && m.embeds.length > 0)
    .first();

  if (existing) {
    await existing.edit({ embeds: [embed], components: [buttonRow] });
    return existing;
  } else {
    return await channel.send({ embeds: [embed], components: [buttonRow] });
  }
}

async function createDraftLolLobby() {
  return new Promise((resolve, reject) => {
    const roomId = generateRandomString(8);
    const password = generateRandomString(8);
    const blueCode = generateRandomString(8);
    const redCode = generateRandomString(8);
    
    const baseUrl = 'https://draftlol.dawe.gg';
    const lobbyUrl = `${baseUrl}/${roomId}/${password}/${blueCode}/${redCode}`;
    
    const links = {
      lobby: lobbyUrl,
      blue: `${baseUrl}/${roomId}/${blueCode}`,
      red: `${baseUrl}/${roomId}/${redCode}`,
      spectator: `${baseUrl}/${roomId}`
    };

    console.log('🔄 Attempting WebSocket connection to create draft room...');
    
    const ws = new WebSocket('wss://draftlol.dawe.gg/');
    let roomCreated = false;

    ws.on('open', () => {
      console.log('🔗 WebSocket connected, joining room:', roomId);
      
      // Join the room first
      ws.send(JSON.stringify({
        type: "joinroom",
        roomId: roomId,
        password: password
      }));
    });

    ws.on('message', (data) => {
      try {
        const message = JSON.parse(data.toString());
        console.log('📨 Received:', message.type);
        
        if (message.type === 'statechange') {
          console.log('✅ Room state received - room is active');
          roomCreated = true;
          ws.close();
          resolve(links);
        } else if (message.type === 'error') {
          console.log('❌ WebSocket error:', message);
          // Even if there's an error, we'll still return the links
          // Sometimes the room still gets created
          if (!roomCreated) {
            roomCreated = true;
            ws.close();
            resolve(links);
          }
        }
      } catch (error) {
        console.error('Error parsing WebSocket message:', error);
      }
    });

    ws.on('error', (error) => {
      console.error('WebSocket connection error:', error);
      if (!roomCreated) {
        roomCreated = true;
        resolve(links); // Fallback to returning links anyway
      }
    });

    ws.on('close', () => {
      console.log('🔌 WebSocket closed');
      if (!roomCreated) {
        console.log('⚠️ WebSocket closed before room creation, using generated links');
        resolve(links);
      }
    });

    // Timeout after 5 seconds
    setTimeout(() => {
      if (!roomCreated) {
        console.log('⏰ WebSocket timeout, using generated links');
        roomCreated = true;
        ws.close();
        resolve(links);
      }
    }, 5000);
  });
}

function generateRandomString(length = 8) {
  const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
  let result = '';
  for (let i = 0; i < length; i++) {
    result += chars.charAt(Math.floor(Math.random() * chars.length));
  }
  return result;
}

client.rest.on('rateLimited', (rateLimitInfo) => {
    console.log('🚨 RATE LIMIT HIT - Countdown may freeze:', {
        route: rateLimitInfo.route,
        timeToReset: rateLimitInfo.timeToReset + 'ms',
        retryAfter: rateLimitInfo.retryAfter + 'ms'
    });
});

// Add to your client setup
client.on("error", (error) => {
    console.error("Global client error:", error);
});

// Handle uncaught exceptions
process.on("uncaughtException", (error) => {
    console.error("Uncaught Exception:", error);
});

process.on("unhandledRejection", (reason, promise) => {
    console.error("Unhandled Rejection at:", promise, "reason:", reason);
});

function buildQueueEmbed() {
  const embed = new EmbedBuilder()
    .setTitle("🎮 Current Queue")
    .setColor(queueEnabled ? 0x00ff00 : 0xff0000)
    .setDescription(
      (queue.length ? queue.map((id, i) => `${i + 1}. <@${id}>`).join("\n") : "The queue is currently empty.") +
      `\n\nStatus: **${queueEnabled ? "OPEN" : "CLOSED"}**`
    )
    .setFooter({ text: `Queue Size: ${queue.length}/${QUEUE_SIZE}` })
    .setTimestamp();
  return embed;
}

// ---------------- QUEUE EMBED ----------------
async function postQueueMessage(channel) {
  // Check for an existing queue message (from the bot)
  const existing = (await channel.messages.fetch({ limit: 10 }))
    .filter(m => m.author.id === client.user.id && m.embeds.length && m.embeds[0].title === "🎮 Current Queue")
    .first();

  if (existing) {
    console.log("Queue message already exists — reusing it.");
    queueMessage = existing;
    await updateQueueMessage();
    return;
  }

  // Otherwise, create a new queue message
  const row = new ActionRowBuilder().addComponents(
    new ButtonBuilder().setCustomId("join").setLabel("✅ Join Queue").setStyle(ButtonStyle.Success),
    new ButtonBuilder().setCustomId("leave").setLabel("🚪 Leave Queue").setStyle(ButtonStyle.Danger),
    new ButtonBuilder().setCustomId("opgg").setLabel("🌐 Multi OP.GG").setStyle(ButtonStyle.Primary)
  );

  const embed = buildQueueEmbed();
  queueMessage = await channel.send({ embeds: [embed], components: [row] });
}

let updateQueueTimeout = null;
async function updateQueueMessage() {
  trackRequest();
  if (!queueMessage) return;

  // Debounce rapid updates
  if (updateQueueTimeout) {
    clearTimeout(updateQueueTimeout);
  }

  updateQueueTimeout = setTimeout(async () => {
    // dynamically rebuild the Multi OP.GG link
    const getMultiOPGG = () => {
      const summoners = queue
        .map((id) => playerData[id]?.summonerName)
        .filter(Boolean)
        .map((url) => {
          try {
            const parts = url.split("/");
            const namePart = decodeURIComponent(parts[parts.length - 1]);
            return namePart.replace("-", "%23").replace(/\s+/g, "+");
          } catch {
            return null;
          }
        })
        .filter(Boolean);
      if (summoners.length === 0) return "https://www.op.gg/";
      return `https://www.op.gg/lol/multisearch/na?summoners=${summoners.join("%2C")}`;
    };

    const row = new ActionRowBuilder().addComponents(
      new ButtonBuilder().setCustomId("join").setLabel("✅ Join Queue").setStyle(ButtonStyle.Success),
      new ButtonBuilder().setCustomId("leave").setLabel("🚪 Leave Queue").setStyle(ButtonStyle.Danger),
      new ButtonBuilder().setLabel("🌐 Multi OP.GG").setStyle(ButtonStyle.Link).setURL(getMultiOPGG())
    );

    const embed = buildQueueEmbed();
    await queueMessage.edit({ embeds: [embed], components: [row] });
  }, 250); // Wait 250ms after last change
}

// Helper function to update match message with vote display
async function updateMatchVoteDisplay(channel, match) {
  if (!match.matchMessageId) return;
  
  try {
    const matchMessage = await channel.messages.fetch(match.matchMessageId);
    const embed = matchMessage.embeds[0];
    const team1Votes = match.votes.team1.size;
    const team2Votes = match.votes.team2.size;
    const totalVotes = team1Votes + team2Votes;
    
    // Create a new embed with vote information
    const updatedEmbed = EmbedBuilder.from(embed)
      .addFields({
        name: "🗳️ Match Voting",
        value: `🔵 Team 1: ${team1Votes} votes\n🔴 Team 2: ${team2Votes} votes\n📊 Total: ${totalVotes}/10 players\n\n*6 votes for one team ends the match*`,
        inline: false
      });
    
    await matchMessage.edit({ embeds: [updatedEmbed] });
  } catch (error) {
    console.error("Failed to update match vote display:", error);
  }
}

// ---------------- CONSOLE LOGGING FUNCTION ----------------
function logRoleAssignmentToConsole(bestTeam1, bestTeam2, team1Roles, team2Roles, team1Satisfaction, team2Satisfaction) {
  console.log('\n🎯 ===== ROLE ASSIGNMENT ANALYTICS =====');
  console.log(`📅 Match created at: ${new Date().toLocaleString()}`);
  
  function formatPlayerDetails(team, roles, teamName) {
    console.log(`\n${teamName}:`);
    team.forEach(playerId => {
      const player = playerData[playerId];
      const assignedRole = roles[playerId];
      const preferenceIndex = player.roles?.indexOf(assignedRole) ?? -1;
      const points = preferenceIndex >= 0 ? preferenceIndex + 1 : (player.roles?.includes("Fill") ? 3 : 5);
      const isPerfect = preferenceIndex === 0;
      
      console.log(`  • ${playerId}: ${assignedRole} (${points} pts) - ${player.roles?.join(' → ') || 'No prefs'} ${isPerfect ? '⭐ PERFECT' : ''}`);
    });
  }

  formatPlayerDetails(bestTeam1, team1Roles, '🔵 TEAM 1');
  formatPlayerDetails(bestTeam2, team2Roles, '🔴 TEAM 2');
  
  const team1Perfect = bestTeam1.filter(id => playerData[id].roles?.indexOf(team1Roles[id]) === 0).length;
  const team2Perfect = bestTeam2.filter(id => playerData[id].roles?.indexOf(team2Roles[id]) === 0).length;
  
  console.log('\n📊 SUMMARY:');
  console.log(`  Team 1: ${team1Satisfaction.totalPoints} total points, ${team1Perfect}/5 perfect roles`);
  console.log(`  Team 2: ${team2Satisfaction.totalPoints} total points, ${team2Perfect}/5 perfect roles`);
  console.log(`  Point Difference: ${Math.abs(team1Satisfaction.totalPoints - team2Satisfaction.totalPoints)}`);
  console.log(`  Combined Perfect: ${team1Perfect + team2Perfect}/10`);
  console.log('🎯 ===== END ROLE ASSIGNMENT =====\n');
}

client.on("interactionCreate", async (interaction) => {
  // ---------------- BUTTONS ----------------
  if (interaction.isButton()) {
    const id = interaction.user.id;
    // --- Report Win Buttons ---
    if (interaction.customId === 'open_role_selection') {
        try {
            // Defer immediately to extend response time to 15 minutes
            await interaction.deferReply({ ephemeral: true });
            
            const embed = new EmbedBuilder()
                .setTitle("🎮 Set Your Role Preferences")
                .setDescription("**Select your 5 preferred roles in order**\n\n1️⃣ = Most preferred\n5️⃣ = Least preferred\n\n*Selecting 'Fill' will automatically fill all subsequent roles*\n\n**Note:** You cannot select the same role twice!")
                .setColor(0x0099FF);

            const rows = [];
            
            for (let i = 1; i <= 5; i++) {
                const selectMenu = new StringSelectMenuBuilder()
                    .setCustomId(`role_select_${i}`)
                    .setPlaceholder(`Position ${i}${i === 1 ? ' (Most Preferred)' : i === 5 ? ' (Least Preferred)' : ''}`)
                    .addOptions(
                        ROLES.map(role => 
                            new StringSelectMenuOptionBuilder()
                                .setLabel(role.label)
                                .setValue(role.value)
                        )
                    );
                
                rows.push(new ActionRowBuilder().addComponents(selectMenu));
            }

            // Use editReply instead of reply since we deferred
            await interaction.editReply({
                embeds: [embed],
                components: rows
            });
            
        } catch (error) {
            console.error("Error in role selection:", error);
            // If deferral failed, try a fallback response
            if (!interaction.deferred && !interaction.replied) {
                await interaction.reply({
                    content: "❌ Failed to open role selection. Please try again.",
                    ephemeral: true
                }).catch(() => {}); // Ignore errors in error handling
            }
        }
        return;
    }

    const [type, team, topPlayerId] = interaction.customId.split("_");
    ensurePlayer(id);

    // --- Join Queue ---
    if (interaction.customId === "join") {
      if (bannedUsers.has(interaction.user.id)) {
        return interaction.reply({
          content: "🚫 You are banned from queuing. Contact an admin if you believe this is a mistake.",
          ephemeral: true,
        });
      }

      // ADD THIS CHECK - Prevent users in timeout from joining queue
      const timeoutStatus = isUserInTimeout(interaction.user.id);
      if (timeoutStatus.inTimeout) {
        const timeLeft = formatTimeLeft(timeoutStatus.timeLeft);
        return interaction.reply({
          content: `⏰ You are currently in a timeout penalty and cannot join the queue for ${timeLeft}.`,
          ephemeral: true,
        });
      }

      // ADD THIS CHECK - Prevent joining when ready check is active
      if (activeReadyCheck) {
        return interaction.reply({
          content: "⏳ A ready check is currently in progress. Please wait for it to complete before joining the queue.",
          ephemeral: true,
        });
      }

      // ADD SOLUTION 1: Queue Locking
      if (queueLock) {
        return interaction.reply({
          content: "⏳ The queue is currently processing. Please try again in a moment.",
          ephemeral: true,
        });
      }

      // Check for block conflicts BEFORE joining
      const blockConflicts = checkQueueForBlocks(id);
      if (blockConflicts.length > 0) {
        const blockedUsersList = blockConflicts.map(blockedId => `<@${blockedId}>`).join(', ');
        return interaction.reply({
          content: `🚫 You cannot join the queue because you have blocked ${blockedUsersList}. They must leave the queue first, or you need to unblock them.`,
          ephemeral: true,
        });
      }

      if (!queueEnabled) { 
        return interaction.reply({ 
          content: "⚠️ The queue is currently **closed**. You cannot join at this time.", 
          ephemeral: true, 
        }); 
      }
      
      // Prevent joining if already in ANY active match
      const isInAnyMatch = Array.from(matches.values()).some(match => 
        match.team1.includes(id) || match.team2.includes(id)
      );
      
      if (isInAnyMatch) {
        return interaction.reply({
          content: "⚠️ You are currently in an active match and cannot join the queue until it ends.",
          ephemeral: true,
        });
      }

      const player = playerData[id];
      if (!player || !player.summonerName) {
        return interaction.reply({
          content: "❌ You must **register** first with !register <OP.GG link> before joining the queue.",
          ephemeral: true,
        });
      }

      // Enhanced role verification
      if (!player.roles || player.roles.length < 5 || player.roles.some(r => !r)) {
        const missingRolesEmbed = new EmbedBuilder()
          .setTitle("❌ Role Preferences Incomplete")
          .setDescription("You must set all 5 role preferences before joining the queue.")
          .addFields(
            { 
              name: "Current Status", 
              value: player.roles ? 
                player.roles.map((r, i) => `${i + 1}. ${r || "❌ Not set"}`).join('\n') : 
                "No roles set" 
            },
            { 
              name: "How to Fix", 
              value: "Click the '🎮 Set Roles' button in the how-to-play channel to complete your role preferences." 
            }
          )
          .setColor(0xFF0000);

        return interaction.reply({
          embeds: [missingRolesEmbed],
          ephemeral: true
        });
      }

      // ADD SOLUTION 1 & 2: Queue Locking with Atomic Operations
      try {
        // LOCK THE QUEUE
        queueLock = true;
        
        // Double-check queue status after lock
        if (queue.includes(id)) {
          queueLock = false;
          return interaction.reply({ content: "⚠️ You're already in the queue.", ephemeral: true });
        }

        // ADD SOLUTION 2: Atomic Queue Size Check
        if (queue.length >= QUEUE_SIZE) {
          queueLock = false;
          return interaction.reply({ 
            content: "⚠️ The queue is already full. Please wait for the next queue", 
            ephemeral: true 
          });
        }

        queue.push(id);
        saveData();
        await updateQueueMessage();
        
        // ADD SOLUTION 3: Strict Ready Check Trigger
        if (queue.length === QUEUE_SIZE && !activeReadyCheck) {
          await startReadyCheck(interaction.channel);
        }
        
        await interaction.deferUpdate().catch(err => { 
          if (err.code !== 10062) console.error("deferUpdate failed:", err); 
        });
        
      } finally {
        // UNLOCK THE QUEUE
        queueLock = false;
      }
    }

    else if (interaction.customId.startsWith("report_win_")) {
      const team = interaction.customId.split("_")[2]; // Gets "1" or "2"
      
      // Find the match for this channel
      const match = matches.get(interaction.channelId);
      if (!match) {
        return interaction.reply({ 
          content: "❌ No active match found in this channel.", 
          ephemeral: true 
        });
      }
      
      const playerId = interaction.user.id;
      const isStaff = interaction.member.permissions.has("ManageGuild");
      
      // STAFF OVERRIDE: Immediate win
      if (isStaff) {
        await endMatch(interaction.channel, team);
        return interaction.reply({ 
          content: `✅ Staff override: Match result recorded! Team ${team} wins!`, 
          ephemeral: true 
        });
      }
      
      // PLAYER VOTING: Check if player is in this match
      const isInMatch = match.team1.includes(playerId) || match.team2.includes(playerId);
      if (!isInMatch) {
        return interaction.reply({ 
          content: "❌ You are not a player in this match and cannot vote.", 
          ephemeral: true 
        });
      }
      
      // Remove previous votes from this player
      match.votes.team1.delete(playerId);
      match.votes.team2.delete(playerId);
      
      // Add new vote
      if (team === "1") {
        match.votes.team1.add(playerId);
      } else {
        match.votes.team2.add(playerId);
      }
      
      // Check if we have enough votes (6 out of 10 players)
      const totalVotes = match.votes.team1.size + match.votes.team2.size;
      const team1Votes = match.votes.team1.size;
      const team2Votes = match.votes.team2.size;
      
      let voteMessage = `🗳️ You voted for Team ${team}!\n\n`;
      voteMessage += `**Current Vote Count:**\n`;
      voteMessage += `🔵 Team 1: ${team1Votes} votes\n`;
      voteMessage += `🔴 Team 2: ${team2Votes} votes\n`;
      voteMessage += `📊 Total votes: ${totalVotes}/10 players\n\n`;
      
      // Check for win condition (6 votes for one team)
      if (team1Votes >= 6) {
        voteMessage += `🏆 **Team 1 has reached 6 votes! Match ending...**`;
        await interaction.reply({ content: voteMessage, ephemeral: false });
        await endMatch(interaction.channel, "1");
      } else if (team2Votes >= 6) {
        voteMessage += `🏆 **Team 2 has reached 6 votes! Match ending...**`;
        await interaction.reply({ content: voteMessage, ephemeral: false });
        await endMatch(interaction.channel, "2");
      } else {
        voteMessage += `*Need 6 votes for one team to end the match*`;
        await interaction.reply({ content: voteMessage, ephemeral: true });
        
        // Also update the match message to show current votes
        await updateMatchVoteDisplay(interaction.channel, match);
      }
    }

    // --- Leave Queue ---
    else if (interaction.customId === "leave") {
      if (!queue.includes(id)) {
        // Silently ignore if not in queue
        try {
          await interaction.deferUpdate();
        } catch (err) {
          if (err.code !== 10062) console.error("Leave deferUpdate failed:", err);
        }
        return;
      }

      queue = queue.filter((x) => x !== id);
      saveData();
      await updateQueueMessage();

      try {
        await interaction.deferUpdate();
      } catch (err) {
        if (err.code !== 10062) console.error("Leave deferUpdate failed:", err);
      }
    }

    // --- Multi OP.GG ---
    else if (interaction.customId === "opgg") {
      if (queue.length === 0) {
        return interaction.reply({ content: "❌ The queue is empty.", ephemeral: true });
      }
      const summoners = queue
        .map((id) => playerData[id]?.summonerName)
        .filter(Boolean)
        .map((url) => {
          try {
            const parts = url.split("/");
            const namePart = decodeURIComponent(parts[parts.length - 1]);
            return namePart.replace("-", "%23").replace(/\s+/g, "+");
          } catch {
            return null;
          }
        })
        .filter(Boolean);

      if (summoners.length === 0) {
        return interaction.reply({ content: "❌ No registered OP.GG links found.", ephemeral: true });
      }

      const multiLink = `https://www.op.gg/lol/multisearch/na?summoners=${summoners.join("%2C")}`;
      return interaction.reply({ content: `🌐 [Multi OP.GG Link for Queue](${multiLink})`, ephemeral: true });
    }
  }

  // ---------------- SELECT MENUS ----------------
if (interaction.isStringSelectMenu() && interaction.customId.startsWith("role_select_")) {
  const userId = interaction.user.id;
  const slot = parseInt(interaction.customId.split("_").pop(), 10);
  const selectedRole = interaction.values[0];

  ensurePlayer(userId);
  if (!playerData[userId].roles) playerData[userId].roles = Array(5).fill(null);

  // Get current roles to check for duplicates
  const currentRoles = [...playerData[userId].roles];
  
  // If selecting a non-Fill role, remove it from other positions
  if (selectedRole !== "Fill") {
    // Remove this role from all other positions
    for (let i = 0; i < currentRoles.length; i++) {
      if (i !== slot - 1 && currentRoles[i] === selectedRole) {
        playerData[userId].roles[i] = null;
      }
    }
  }

  // Apply smart fill logic
  if (selectedRole === "Fill") {
    for (let i = slot - 1; i < 5; i++) {
      playerData[userId].roles[i] = "Fill";
    }
  } else {
    playerData[userId].roles[slot - 1] = selectedRole;
    // Clear any auto-filled roles after this position
    for (let i = slot; i < 5; i++) {
      if (playerData[userId].roles[i] === "Fill") {
        playerData[userId].roles[i] = null;
      }
    }
  }

  saveData();

  // Update the select menus to reflect changes (disable already selected roles)
  const updatedRows = [];
  
  for (let i = 1; i <= 5; i++) {
    const selectMenu = new StringSelectMenuBuilder()
      .setCustomId(`role_select_${i}`)
      .setPlaceholder(`Position ${i}${i === 1 ? ' (Most Preferred)' : i === 5 ? ' (Least Preferred)' : ''}`);
    
    // Dynamically build options, disabling already-selected roles in other positions
    const options = ROLES.map(role => {
      const option = new StringSelectMenuOptionBuilder()
        .setLabel(role.label)
        .setValue(role.value);
      
      // Disable role if it's already selected in another position (except current position and Fill)
      if (role.value !== "Fill") {
        const isAlreadySelected = playerData[userId].roles.some((existingRole, index) => 
          existingRole === role.value && index !== i - 1
        );
        if (isAlreadySelected) {
          const existingPosition = playerData[userId].roles.findIndex(r => r === role.value) + 1;
          option.setDescription(`Already selected as position ${existingPosition}`);
          option.setDefault(false);
        }
      }
      
      // Mark current selection as default
      if (playerData[userId].roles[i - 1] === role.value) {
        option.setDefault(true);
      }
      
      return option;
    });
    
    selectMenu.addOptions(options);
    updatedRows.push(new ActionRowBuilder().addComponents(selectMenu));
  }

  // Create updated display
  const updatedRoles = playerData[userId].roles;
  const roleDisplay = updatedRoles.map((role, index) => {
    const position = index + 1;
    const emoji = position === 1 ? "1️⃣" : position === 2 ? "2️⃣" : position === 3 ? "3️⃣" : position === 4 ? "4️⃣" : "5️⃣";
    return `${emoji} ${role || "❌ Not set"}`;
  }).join('\n');

  const successEmbed = new EmbedBuilder()
    .setTitle("🎮 Set Your Role Preferences")
    .setDescription(`**Position ${slot}** set to: **${selectedRole}**${selectedRole === "Fill" ? " (all subsequent positions auto-filled)" : ""}\n\n**Your Current Preferences:**\n${roleDisplay}\n\n*Selecting 'Fill' will automatically fill all subsequent roles*\n\n**Note:** Roles are automatically moved when selected in new positions`)
    .setColor(0x0099FF);

  // Update the original message with refreshed menus
  await interaction.update({
    embeds: [successEmbed],
    components: updatedRows
  });
  return;
}
});

// ---------------- COMMANDS ----------------
client.on("messageCreate", async (message) => {
  // ---------------- AUTO-DELETE QUEUE CHANNEL MESSAGES ----------------
  // Delete ANY message in queue channel after 60 seconds, except the main queue embed
  if (message.channel.name === 'queue') {
    // ONLY skip deletion for the main queue message (the one with buttons)
    if (message.id === queueMessage?.id) {
      return; // Don't delete the main queue embed
    }
    
    // Don't delete bot messages that are part of ready checks or other important bot messages
    if (message.embeds.length > 0) {
      const embed = message.embeds[0];
      if (embed.title && (embed.title.includes("Ready Check"))) {
        return; // Skip deletion for important bot embeds
      }
    }

    // Schedule deletion after 60 seconds for EVERY OTHER MESSAGE
    setTimeout(() => {
      deleteQueue.addMessage(message);
    }, 60000); // 60 seconds
  }

  if (message.author.bot) return;
  const [cmd, ...args] = message.content.trim().split(/\s+/);

    // ---------------- !register ----------------
    if (cmd === "!register") {
      const userId = message.author.id;
      if (playerData[userId] && playerData[userId].summonerName) {
        return message.reply("❌ You have already registered an account.");
      }

      if (args.length < 1) return message.reply("Usage: !register <OP.GG link>");
      const url = args[0];
      if (!url.includes("op.gg")) return message.reply("❌ Please provide a valid OP.GG link.");

      try {
        const res = await axios.get(url);
        const $ = cheerio.load(res.data);
        const tierText = $("strong.text-xl").first().text().trim();
        const lpText = $("span.text-xs.text-gray-500").first().text().trim();
        const lp = parseInt(lpText);
        if (!tierText || isNaN(lp)) return message.reply("❌ Could not parse rank/LP from OP.GG.");

        let rank, division;
        const tierParts = tierText.trim().split(/\s+/);
        if (tierParts.length === 2) {
          rank = tierParts[0].charAt(0).toUpperCase() + tierParts[0].slice(1).toLowerCase();
          const divText = tierParts[1].toUpperCase();
          const romanToNumber = { IV: 4, III: 3, II: 2, I: 1 };
          division = !isNaN(parseInt(divText)) ? parseInt(divText) : romanToNumber[divText] || 4;
        } else {
          rank = tierParts[0].charAt(0).toUpperCase() + tierParts[0].slice(1).toLowerCase();
          division = null;
        }

        ensurePlayer(userId);
        playerData[userId].summonerName = url;
        playerData[userId].rank = rank;
        playerData[userId].division = division;
        playerData[userId].lp = lp;
        playerData[userId].IHP = getIHP(playerData[userId]);
        saveData();
        await updateLeaderboardChannel(message.guild);
        await message.reply(`✅ Registered ${message.author.username} as **${tierText} ${lp} LP**`);

      } catch (err) {
        console.error(err);
        return message.reply("❌ Failed to fetch OP.GG page. Make sure the link is correct.");
      }
    }
    
    // ---------------- !smurfing (STAFF ONLY) ----------------
    if (cmd === "!smurfing") {
      if (!message.member.permissions.has("ManageGuild")) {
        return message.reply("❌ Only staff members can use this command.");
      }

      if (args.length < 3) {
        return message.reply("Usage: !smurfing @user <registered_rank> <main_rank>");
      }

      const userMention = args[0];
      const registeredRank = args[1];
      const mainRank = args[2];
      
      const smurfUserId = userMention.replace(/[<@!>]/g, "");
      
      if (!smurfUserId) {
        return message.reply("❌ Please provide a valid user mention.");
      }

      try {
        // FIX: More robust initialization of smurf refund tracking
        if (!playerData._smurfRefunds) {
          playerData._smurfRefunds = {
            processedMatches: new Set(),
            processedSmurfs: new Set(),
            refundHistory: {}
          };
        }
        
        // Ensure all required properties exist
        if (!playerData._smurfRefunds.processedMatches) {
          playerData._smurfRefunds.processedMatches = new Set();
        }
        if (!playerData._smurfRefunds.processedSmurfs) {
          playerData._smurfRefunds.processedSmurfs = new Set();
        }
        if (!playerData._smurfRefunds.refundHistory) {
          playerData._smurfRefunds.refundHistory = {};
        }

        // Check if this smurf has already been processed
        if (playerData._smurfRefunds.processedSmurfs.has(smurfUserId)) {
          return message.reply("⚠️ This user has already been processed as a smurf. Refunds have already been applied.");
        }

        // Load match history to find all matches involving the smurf
        const matchHistory = loadMatchHistory();
        
        // Find all matches where the smurf player participated
        const smurfMatches = matchHistory.filter(match => 
          (match.team1.includes(smurfUserId) || match.team2.includes(smurfUserId)) && 
          !match.voided
        );

        if (smurfMatches.length === 0) {
          return message.reply("❌ No matches found for this user, or all matches are already voided.");
        }

        let refundedMatches = 0;
        let playersWithLossesRemoved = 0;
        let playersWithEloRefunded = 0;
        
        // Track ELO refunded per player (each player can get up to 100 ELO)
        const playerRefundTotals = new Map();
        const MAX_ELO_PER_PLAYER = 100; // Each player can get up to 100 ELO total

        // Store refund details for potential reversal
        const refundDetails = [];

        // Process each match the smurf played in
        for (const match of smurfMatches) {
          const wasInTeam1 = match.team1.includes(smurfUserId);
          const opposingTeam = wasInTeam1 ? match.team2 : match.team1;
          
          // Refund ELO to opposing team players
          for (const playerId of opposingTeam) {
            const matchEloChange = match.eloChanges.find(change => change.id === playerId);
            
            if (matchEloChange && !matchEloChange.isWinner) {
              // Create a unique identifier for this match-player combination
              const refundKey = `${match.id}_${playerId}`;
              
              // Skip if this match-player combination has already been refunded
              if (playerData._smurfRefunds.processedMatches.has(refundKey)) {
                continue;
              }

              // Ensure player exists and has proper data structure
              const player = ensurePlayer(playerId);
              
              // Store original state for potential reversal
              const originalState = {
                playerId: playerId,
                matchId: match.id,
                oldLosses: player.losses,
                oldIHP: getIHP(player),
                oldRank: player.rank,
                oldDivision: player.division,
                oldLP: player.lp,
                refundAmount: 0
              };
              
              // ALWAYS remove the loss from their record (no cap on this)
              player.losses = Math.max(0, player.losses - 1);
              playersWithLossesRemoved++;
              
              // Get how much ELO this player has already received
              const alreadyRefunded = playerRefundTotals.get(playerId) || 0;
              const remainingForPlayer = MAX_ELO_PER_PLAYER - alreadyRefunded;
              
              if (remainingForPlayer > 0) {
                // Calculate the original ELO loss from the match
                const originalEloLoss = Math.abs(matchEloChange.change);
                
                // Only refund what the player has left in their personal budget
                const actualRefundIHP = Math.min(originalEloLoss, remainingForPlayer);
                
                // Apply ELO refund
                const currentIHP = getIHP(player);
                const newIHP = currentIHP + actualRefundIHP;
                const newStats = IHPToRank(newIHP);
                
                // Safely update player stats
                if (newStats) {
                  player.rank = newStats.rank || player.rank;
                  player.division = newStats.division !== undefined ? newStats.division : player.division;
                  player.lp = newStats.lp !== undefined ? newStats.lp : player.lp;
                }
                
                // Update player's refund total
                playerRefundTotals.set(playerId, alreadyRefunded + actualRefundIHP);
                originalState.refundAmount = actualRefundIHP;
                
                if (actualRefundIHP > 0) {
                  playersWithEloRefunded++;
                }
              }

              // Store refund details for potential reversal
              refundDetails.push(originalState);

              // Mark this match-player combination as processed
              playerData._smurfRefunds.processedMatches.add(refundKey);
            }
          }
          
          refundedMatches++;
        }

        // If no new refunds were processed, don't proceed
        if (playersWithLossesRemoved === 0) {
          return message.reply("⚠️ All matches involving this user have already been processed for smurf refunds. No new refunds applied.");
        }

        // Calculate total ELO refunded across all players
        const totalEloRefunded = Array.from(playerRefundTotals.values()).reduce((sum, refund) => sum + refund, 0);

        // Store the complete refund history for this smurf
        playerData._smurfRefunds.refundHistory[smurfUserId] = {
          timestamp: Date.now(),
          processedBy: message.author.id,
          registeredRank: registeredRank,
          mainRank: mainRank,
          refundDetails: refundDetails,
          playerRefundTotals: Array.from(playerRefundTotals.entries()),
          totalEloRefunded: totalEloRefunded,
          playersWithLossesRemoved: playersWithLossesRemoved,
          playersWithEloRefunded: playersWithEloRefunded,
          refundedMatches: refundedMatches
        };

        // Mark this smurf as processed
        playerData._smurfRefunds.processedSmurfs.add(smurfUserId);

        // Ban the smurf user
        await message.guild.members.ban(smurfUserId, {
          reason: `Smurfing: Registered as ${registeredRank} but main is ${mainRank}`
        });

        // Save all changes
        saveData();
        await updateLeaderboardChannel(message.guild);

        // Build player refund list (ALL players who received ELO)
        const playersWithRefunds = Array.from(playerRefundTotals.entries())
          .filter(([_, total]) => total > 0) // Only include players who actually got ELO
          .sort((a, b) => b[1] - a[1]);

        // Create embeds array
        const embeds = [];

        // Main summary embed
        let summaryReport = `**🚫 Smurfing Ban**\n\n`;
        summaryReport += `**User:** <@${smurfUserId}>\n`;
        summaryReport += `**Registered As:** ${registeredRank}\n`;
        summaryReport += `**Main Account:** ${mainRank}\n\n`;
        summaryReport += `**Actions Taken:**\n`;
        summaryReport += `✅ User permanently banned\n`;
        summaryReport += `✅ ${refundedMatches} matches processed\n`;
        summaryReport += `✅ ${playersWithLossesRemoved} players had losses removed & Elo refunded\n`;
        summaryReport += `💰 ${totalEloRefunded} total Elo refunded\n\n`;
        
        // Show players who hit the cap
        const playersAtCap = playersWithRefunds.filter(([_, total]) => total >= MAX_ELO_PER_PLAYER).length;
        
        if (playersAtCap > 0) {
          summaryReport += `**Summary:** ${playersAtCap} player(s) reached the maximum 100 ELO refund.\n\n`;
        }
        
        if (playersWithRefunds.length > 0) {
          summaryReport += `**Players Receiving ELO Refunds:**\n`;
        } else {
          summaryReport += `**Note:** All eligible players had already reached the 100 ELO refund cap. Teammates of the smurf will keep their Elo & wins.\n`;
        }

        const summaryEmbed = new EmbedBuilder()
          .setTitle("🚫 Public Execution")
          .setDescription(summaryReport)
          .setColor(0xff0000)
          .setTimestamp()
          .setFooter({ text: "Anti-smurfing enforcement" });

        embeds.push(summaryEmbed);

        // Function to add player refunds to embeds
        function addPlayerRefundsToEmbeds(players) {
          if (players.length === 0) return;

          let currentEmbedIndex = 0;
          let currentContent = "";
          
          for (const [playerId, totalRefund] of players) {
            const playerLine = `• <@${playerId}>: +${totalRefund} ELO${totalRefund >= MAX_ELO_PER_PLAYER ? ' ✅ (Max reached)' : ''}\n`;
            
            // Check if adding this line would exceed the limit
            if ((currentContent + playerLine).length > 4096) {
              // Start a new embed
              currentEmbedIndex++;
              currentContent = playerLine;
              
              const newEmbed = new EmbedBuilder()
                .setTitle(`🚫 Smurfing Ban (Refunds Continued)`)
                .setDescription(currentContent)
                .setColor(0xff0000)
                .setFooter({ text: `Part ${currentEmbedIndex + 1}` });
              
              embeds.push(newEmbed);
            } else {
              currentContent += playerLine;
              
              // Update the current embed
              if (currentEmbedIndex === 0) {
                // If this is the first embed, we need to combine with summary
                embeds[0].setDescription(summaryReport + currentContent);
              } else {
                embeds[currentEmbedIndex].setDescription(currentContent);
              }
            }
          }
        }

        // Add player refunds to embeds (only players who actually received ELO)
        addPlayerRefundsToEmbeds(playersWithRefunds);

        // Find general channel and send notification
        const generalChannel = message.guild.channels.cache.find(
          channel => channel.name === "general" && channel.type === 0
        );

        if (generalChannel) {
          await generalChannel.send({ embeds: embeds });
        }

        // Confirm to the staff member
        let confirmation = `✅ Smurfing penalty executed for <@${smurfUserId}>. ${refundedMatches} matches processed, ${playersWithLossesRemoved} players had losses removed`;
        
        if (playersWithEloRefunded > 0) {
          confirmation += `, ${playersWithEloRefunded} players received ${totalEloRefunded} ELO total`;
        }
        
        const playersAtCapCount = playersWithRefunds.filter(([_, total]) => total >= MAX_ELO_PER_PLAYER).length;
        
        if (playersAtCapCount > 0) {
          confirmation += ` (${playersAtCapCount} players reached 100 ELO cap)`;
        }
        
        confirmation += `. Notification sent to #general.`;
        confirmation += `\n\nUse \`!undosmurfing @${smurfUserId}\` to reverse this action if needed.`;
        
        await message.channel.send(confirmation);

      } catch (error) {
        console.error("Error processing smurfing penalty:", error);
        if (error.code === 50013) {
          return message.reply("❌ I don't have permission to ban users. Please check my role permissions.");
        } else if (error.code === 10007) {
          return message.reply("❌ That user doesn't exist in this server.");
        } else {
          return message.reply("❌ Failed to process smurfing penalty. Check console for details.");
        }
      }
    }

    // ---------------- !undosmurfing (STAFF ONLY) ----------------
    if (cmd === "!undosmurfing") {
      if (!message.member.permissions.has("ManageGuild")) {
        return message.reply("❌ Only staff members can use this command.");
      }

      if (args.length < 1) {
        return message.reply("Usage: !undosmurfing @user");
      }

      const userMention = args[0];
      const smurfUserId = userMention.replace(/[<@!>]/g, "");
      
      if (!smurfUserId) {
        return message.reply("❌ Please provide a valid user mention.");
      }

      try {
        // Check if smurf refund tracking exists
        if (!playerData._smurfRefunds || !playerData._smurfRefunds.refundHistory) {
          return message.reply("❌ No smurf refund history found. Cannot undo.");
        }

        // Check if this user was processed as a smurf
        const refundHistory = playerData._smurfRefunds.refundHistory[smurfUserId];
        if (!refundHistory) {
          return message.reply("❌ No smurfing penalty found for this user.");
        }

        // Unban the user first
        try {
          await message.guild.members.unban(smurfUserId, "Smurfing penalty reversed");
        } catch (error) {
          if (error.code !== 10026) { // Unknown Ban (user not banned)
            console.error("Error unbanning user:", error);
          }
        }

        // NEW: Track how many losses were actually restored per player
        const playerLossRestoreCount = new Map();
        let reversedPlayers = 0;
        let reversedElo = 0;

        // First, count how many losses each player had removed originally
        for (const refundDetail of refundHistory.refundDetails) {
          const playerId = refundDetail.playerId;
          playerLossRestoreCount.set(playerId, (playerLossRestoreCount.get(playerId) || 0) + 1);
        }

        // Now restore the losses and ELO
        for (const refundDetail of refundHistory.refundDetails) {
          const player = ensurePlayer(refundDetail.playerId);
          
          // Restore original losses - but only if we haven't already restored them
          // We need to check the current state to avoid over-restoring
          const expectedLosses = refundDetail.oldLosses;
          
          // If current losses are less than expected, restore the difference
          if (player.losses < expectedLosses) {
            const lossesToRestore = expectedLosses - player.losses;
            player.losses = expectedLosses;
            console.log(`🔄 Restored ${lossesToRestore} losses for ${refundDetail.playerId}: ${player.losses - lossesToRestore} -> ${player.losses}`);
          }
          
          // Restore original ELO if ELO was refunded
          if (refundDetail.refundAmount > 0) {
            const currentIHP = getIHP(player);
            const restoredIHP = currentIHP - refundDetail.refundAmount;
            const restoredStats = IHPToRank(restoredIHP);
            
            player.rank = restoredStats.rank;
            player.division = restoredStats.division;
            player.lp = restoredStats.lp;
            
            reversedElo += refundDetail.refundAmount;
            console.log(`🔄 Restored ${refundDetail.refundAmount} ELO for ${refundDetail.playerId}`);
          }
          
          // Remove from processed matches
          const refundKey = `${refundDetail.matchId}_${refundDetail.playerId}`;
          playerData._smurfRefunds.processedMatches.delete(refundKey);
          
          reversedPlayers++;
        }

        // Remove from processed smurfs and refund history
        playerData._smurfRefunds.processedSmurfs.delete(smurfUserId);
        delete playerData._smurfRefunds.refundHistory[smurfUserId];

        // Save all changes
        saveData();
        await updateLeaderboardChannel(message.guild);

        // Build embeds array for multi-embed support
        const embeds = [];

        // Main summary embed
        let summaryReport = `**User:** <@${smurfUserId}>\n`;
        summaryReport += `**Originally Flagged As:** ${refundHistory.registeredRank} → ${refundHistory.mainRank}\n\n`;
        summaryReport += `**Reversal Actions:**\n`;
        summaryReport += `✅ User unbanned\n`;
        summaryReport += `✅ ${refundHistory.refundedMatches} matches reversed\n`;
        
        // Show players with multiple losses restored
        const playersWithMultipleLosses = Array.from(playerLossRestoreCount.entries())
          .filter(([_, count]) => count > 1);
        
        if (playersWithMultipleLosses.length > 0) {
          summaryReport += `📊 ${playersWithMultipleLosses.length} players had multiple losses restored\n`;
        }
        
        summaryReport += `✅ ${reversedPlayers} total loss/Elo adjustments reversed\n`;
        summaryReport += `💰 ${reversedElo} total Elo reversed\n\n`;
        
        // Show players who had losses restored (grouped by count)
        if (playerLossRestoreCount.size > 0) {
          summaryReport += `**Players Affected by Reversal:**\n`;
        } else {
          summaryReport += `**Note:** No players had losses to restore.\n`;
        }

        const summaryEmbed = new EmbedBuilder()
          .setTitle("✅ Smurfing Penalty Reversed")
          .setDescription(summaryReport)
          .setColor(0x00ff00) // Green color for reversal
          .setTimestamp()
          .setFooter({ text: "Smurfing penalty reversed" });

        embeds.push(summaryEmbed);

        // Function to add player loss restoration details to embeds
        function addPlayerLossesToEmbeds(playersByLossCount) {
          if (Object.keys(playersByLossCount).length === 0) return;

          let currentEmbedIndex = 0;
          let currentContent = "";
          
          // Sort by loss count (highest first)
          const sortedLossCounts = Object.keys(playersByLossCount).sort((a, b) => b - a);
          
          for (const lossCount of sortedLossCounts) {
            const playerIds = playersByLossCount[lossCount];
            const lossText = lossCount === "1" ? "1 loss" : `${lossCount} losses`;
            
            for (const playerId of playerIds) {
              const playerLine = `• <@${playerId}>: ${lossText} restored\n`;
              
              // Check if adding this line would exceed the limit
              if ((currentContent + playerLine).length > 4096) {
                // Start a new embed
                currentEmbedIndex++;
                currentContent = playerLine;
                
                const newEmbed = new EmbedBuilder()
                  .setTitle(`✅ Smurfing Penalty Reversed (Players Continued)`)
                  .setDescription(currentContent)
                  .setColor(0x00ff00)
                  .setFooter({ text: `Part ${currentEmbedIndex + 1}` });
                
                embeds.push(newEmbed);
              } else {
                currentContent += playerLine;
                
                // Update the current embed
                if (currentEmbedIndex === 0) {
                  // If this is the first additional embed, we need to update the summary
                  // or create a new one if summary is already full
                  if (embeds.length === 1) {
                    // Create first additional embed
                    const firstAdditionalEmbed = new EmbedBuilder()
                      .setTitle(`✅ Smurfing Penalty Reversed (Players)`)
                      .setDescription(currentContent)
                      .setColor(0x00ff00)
                      .setFooter({ text: "Part 2" });
                    
                    embeds.push(firstAdditionalEmbed);
                    currentEmbedIndex = 1;
                  } else {
                    // Update existing additional embed
                    embeds[currentEmbedIndex].setDescription(currentContent);
                  }
                } else {
                  embeds[currentEmbedIndex].setDescription(currentContent);
                }
              }
            }
          }
        }

        // Group players by number of losses restored
        const playersByLossCount = {};
        for (const [playerId, lossCount] of playerLossRestoreCount) {
          if (!playersByLossCount[lossCount]) {
            playersByLossCount[lossCount] = [];
          }
          playersByLossCount[lossCount].push(playerId);
        }

        // Add player loss restoration details to embeds
        addPlayerLossesToEmbeds(playersByLossCount);

        // Find general channel and send reversal notification
        const generalChannel = message.guild.channels.cache.find(
          channel => channel.name === "general" && channel.type === 0
        );

        if (generalChannel) {
          await generalChannel.send({ embeds: embeds });
        }

        // Enhanced confirmation to the staff member
        let confirmation = `✅ Smurfing penalty reversed for <@${smurfUserId}>.\n`;
        confirmation += `• ${refundHistory.refundedMatches} matches reversed\n`;
        confirmation += `• ${playerLossRestoreCount.size} players had losses restored\n`;
        
        // Show players with multiple losses
        const multiLossPlayers = Array.from(playerLossRestoreCount.entries())
          .filter(([_, count]) => count > 1);
        
        if (multiLossPlayers.length > 0) {
          confirmation += `• ${multiLossPlayers.length} players had multiple losses restored\n`;
        }
        
        if (reversedElo > 0) {
          confirmation += `• ${reversedElo} ELO reversed total`;
        }
        
        confirmation += `\n\n${embeds.length} embed(s) sent to #general.`;
        
        await message.channel.send(confirmation);

      } catch (error) {
        console.error("Error reversing smurfing penalty:", error);
        return message.reply("❌ Failed to reverse smurfing penalty. Check console for details.");
      }
    }

    // ---------------- !forcejoin (STAFF ONLY) ----------------
  if (cmd === "!forcejoin") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    if (args.length === 0) {
      return message.reply("Usage: !forcejoin <@user1> <@user2> ... <@userN>");
    }

    // ADD THIS CHECK - Prevent force joining when ready check is active
    if (activeReadyCheck) {
      return message.reply("⏳ A ready check is currently in progress. Please wait for it to complete before force-adding players.");
    }

    const addedUsers = [];
    const skippedUsers = [];
    const timeoutUsers = [];

    // Process each mentioned user
    for (const userMention of args) {
      const userId = userMention.replace(/[<@!>]/g, "");
      
      // Skip if not a valid user ID
      if (!userId || userId.length < 17) continue;
      
      // Check if user is in timeout
      const timeoutStatus = isUserInTimeout(userId);
      if (timeoutStatus.inTimeout) {
        const timeLeft = formatTimeLeft(timeoutStatus.timeLeft);
        timeoutUsers.push(`<@${userId}> (${timeLeft} remaining)`);
        continue;
      }

      // Check if user is already in queue
      if (queue.includes(userId)) {
        skippedUsers.push(`<@${userId}> (already in queue)`);
        continue;
      }

      // Add user to queue
      ensurePlayer(userId);
      if (!queue.includes(userId)) {
        queue.push(userId);
        addedUsers.push(`<@${userId}>`);
      }
    }

    saveData();

    // Build response message
    let response = "";
    
    if (addedUsers.length > 0) {
      response += `✅ Added to queue: ${addedUsers.join(', ')}\n`;
    }
    
    if (skippedUsers.length > 0) {
      response += `⚠️ Skipped: ${skippedUsers.join(', ')}\n`;
    }
    
    if (timeoutUsers.length > 0) {
      response += `⏰ In timeout: ${timeoutUsers.join(', ')}\n`;
    }

    response += `\nQueue size: ${queue.length}/${QUEUE_SIZE}`;

    await message.channel.send(response);
    await updateQueueMessage();
    
    // ADD SOLUTION 3: Strict Ready Check Trigger
    if (queue.length === QUEUE_SIZE && !activeReadyCheck) {
      await startReadyCheck(message.channel);
    }
  }

  // ---------------- !block (STAFF ONLY) ----------------
  if (cmd === "!block") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    const userMention = args[0];
    if (!userMention) {
      return message.reply("Usage: !block <@user>");
    }

    const blockedUserId = userMention.replace(/[<@!>]/g, "");
    const blockerId = message.author.id;

    if (blockedUserId === blockerId) {
      return message.reply("❌ You cannot block yourself.");
    }

    if (getUserBlocks(blockerId).has(blockedUserId)) {
      return message.reply("⚠️ You have already blocked that user.");
    }

    addBlock(blockerId, blockedUserId);

    // Check if blocked user is in queue and remove blocker if they are
    if (queue.includes(blockedUserId) && queue.includes(blockerId)) {
      queue = queue.filter(id => id !== blockerId);
      saveData();
      await updateQueueMessage();
      
      return message.reply(`✅ You have blocked <@${blockedUserId}>. You have been removed from the queue since they are currently in it.`);
    }

    message.reply(`✅ You have blocked <@${blockedUserId}>. You will not be placed in matches with them.`);
  }

  // ---------------- !unblock (STAFF ONLY) ----------------
  if (cmd === "!unblock") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    const userMention = args[0];
    if (!userMention) {
      return message.reply("Usage: !unblock <@user>");
    }

    const blockedUserId = userMention.replace(/[<@!>]/g, "");
    const blockerId = message.author.id;

    if (!getUserBlocks(blockerId).has(blockedUserId)) {
      return message.reply("⚠️ You haven't blocked that user.");
    }

    removeBlock(blockerId, blockedUserId);
    message.reply(`✅ You have unblocked <@${blockedUserId}>.`);
  }

  // ---------------- !myblocks (STAFF ONLY) ----------------
  if (cmd === "!myblocks") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    const blockerId = message.author.id;
    const blocks = getBlockedUsers(blockerId);

    if (blocks.length === 0) {
      return message.reply("You haven't blocked any users.");
    }

    const blockList = blocks.map(id => `<@${id}>`).join('\n');
    const embed = new EmbedBuilder()
      .setTitle("🚫 Your Blocked Users")
      .setDescription(blockList)
      .setColor(0xff0000)
      .setFooter({ text: `Total blocked: ${blocks.length}` });

    message.channel.send({ embeds: [embed] });
  }

  // ---------------- !blockcheck (STAFF ONLY) ----------------
  if (cmd === "!blockcheck") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    const userMention = args[0] || message.author.id;
    const userId = userMention.replace(/[<@!>]/g, "") || message.author.id;
    
    const blocks = getBlockedUsers(userId);
    const blockingYou = Array.from(userBlocks.entries())
      .filter(([blockerId, blockedSet]) => blockedSet.has(userId))
      .map(([blockerId]) => blockerId);

    const embed = new EmbedBuilder()
      .setTitle("🔍 Block Status")
      .setDescription(`Block information for <@${userId}>`)
      .addFields(
        { 
          name: "Users You've Blocked", 
          value: blocks.length > 0 ? blocks.map(id => `<@${id}>`).join('\n') : "None", 
          inline: true 
        },
        { 
          name: "Users Blocking You", 
          value: blockingYou.length > 0 ? blockingYou.map(id => `<@${id}>`).join('\n') : "None", 
          inline: true 
        }
      )
      .setColor(0x00ff00);

    message.channel.send({ embeds: [embed] });
  }

  // ---------------- !timeoutinfo ----------------
  if (cmd === "!timeoutinfo") {
    const userMention = args[0] || message.author.id;
    const userId = userMention.replace(/[<@!>]/g, "") || message.author.id;
    
    const timeoutInfo = getTimeoutInfo(userId);
    const nextReset = createDiscordTimestamp(playerData._timeoutTracking.weeklyReset, 'F');
    
    const embed = new EmbedBuilder()
      .setTitle("⏰ Timeout Information")
      .setDescription(`Timeout status for <@${userId}>`)
      .addFields(
        { name: "Current Offenses", value: `${timeoutInfo.offenses}`, inline: true },
        { name: "In Timeout", value: timeoutInfo.inTimeout ? "✅ Yes" : "❌ No", inline: true },
        { name: "Weekly Reset", value: nextReset, inline: true }
      );
    
    if (timeoutInfo.inTimeout) {
      const timeoutEnd = Date.now() + timeoutInfo.timeLeft;
      embed.addFields({
        name: "Time Remaining",
        value: `${createDiscordTimestamp(timeoutEnd, 'R')} (${createDiscordTimestamp(timeoutEnd, 'F')})`
      });
    }
    if (timeoutInfo.offenses > 0) {
      embed.addFields({
        name: "Next Timeout Duration",
        value: formatTimeLeft(timeoutInfo.nextTimeout)
      });
    }
  
    embed.setColor(timeoutInfo.inTimeout ? 0xff0000 : 0x00ff00);
    
    await message.channel.send({ embeds: [embed] });
  }

  // ---------------- !cleartimeout ----------------
  if (cmd === "!cleartimeout") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    const userMention = args[0];
    if (!userMention) return message.reply("Usage: !cleartimeout <@user>");

    const userId = userMention.replace(/[<@!>]/g, "");
    
    if (playerData._timeoutTracking.playerTimeouts[userId]) {
      delete playerData._timeoutTracking.playerTimeouts[userId];
      saveData();
      await message.channel.send(`✅ Cleared timeout for <@${userId}>`);
    } else {
      await message.reply("⚠️ That user has no active timeout record.");
    }
  }

  // ---------------- !forcetimeoutreset ----------------
  if (cmd === "!forcetimeoutreset") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    // Force immediate weekly reset
    playerData._timeoutTracking.playerTimeouts = {};
    playerData._timeoutTracking.weeklyReset = Date.now() + WEEKLY_RESET_MS;
    saveData();
    
    await message.channel.send("✅ Force reset all timeouts. Weekly reset scheduled.");
  }

  // ---------------- !forceready ----------------
  if (cmd === "!forceready") {
  if (!message.member.permissions.has("ManageGuild")) {
    return message.reply("❌ Only staff members can use this command.");
  }

  if (!queue || queue.length < QUEUE_SIZE) {
    return message.reply("⚠️ There isn't an active ready check right now.");
  }

  message.channel.send("✅ Force-ready activated — all players are now marked ready!");

  // If there's an active ready-check, stop its collector so the existing
  // end-handler runs (it will call makeTeams). This avoids duplicate calls.
  if (activeReadyCheck && activeReadyCheck.collector) {
    try {
      // Optionally edit the message for immediate feedback and remove buttons
      const curMsg = activeReadyCheck.msg;
      try {
        const infoEmbed = EmbedBuilder.from(curMsg.embeds?.[0] || embed)
          .setDescription("✅ Force-ready activated by staff. Match is starting!")
          .setColor(0x00ff00);
        await curMsg.edit({ embeds: [infoEmbed], components: [] }).catch(() => {});
      } catch (e) { /* ignore UI edit errors */ }

      // Stop collector — use same reason as normal "all_ready" path
      activeReadyCheck.collector.stop("all_ready");
      // don't call makeTeams() here — collector.on('end') will do it.
    } catch (err) {
      console.error("Error stopping active ready check:", err);
      // fallback: if something went wrong and no collector, call makeTeams
      await makeTeams(message.channel);
    }
  } else {
    // No active ready-check object (maybe message not cached) — fallback:
    await makeTeams(message.channel);
  }
}

  // ---------------- !ban ----------------
    if (cmd === "!ban") {
      if (!message.member.permissions.has("ManageGuild")) {
        return message.reply("❌ Only staff members can use this command.");
      }

      const userMention = args[0];
      if (!userMention) return message.reply("Usage: !ban <@user>");

      const userId = userMention.replace(/[<@!>]/g, "");

      if (bannedUsers.has(userId)) {
        return message.reply("⚠️ That user is already banned from queuing.");
      }

      bannedUsers.add(userId);
      saveData();

      // Remove them from queue if they're in it
      if (queue.includes(userId)) {
        queue = queue.filter((id) => id !== userId);
        saveData();
        await updateQueueMessage();
      }

      message.channel.send(`🚫 <@${userId}> has been **banned** from queuing.`);
    }

    // ---------------- !unban ----------------
    if (cmd === "!unban") {
      if (!message.member.permissions.has("ManageGuild")) {
        return message.reply("❌ Only staff members can use this command.");
      }

      const userMention = args[0];
      if (!userMention) return message.reply("Usage: !unban <@user>");

      const userId = userMention.replace(/[<@!>]/g, "");

      if (!bannedUsers.has(userId)) {
        return message.reply("⚠️ That user is not currently banned.");
      }

      bannedUsers.delete(userId);
      saveData();

      message.channel.send(`✅ <@${userId}> has been **unbanned** and can queue again.`);
    }

  if (cmd === "!remove") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ You need Manage Server permissions to do that.");
    }
    const userMention = args[0];
    if (!userMention) return message.reply("Usage: !removefromqueue <@user>");
    const userId = userMention.replace(/[<@!>]/g, "");
    if (!queue.includes(userId)) {
      return message.reply("⚠️ That user is not in the queue.");
    }
    queue = queue.filter((id) => id !== userId);
    saveData();
    await updateQueueMessage();
    return message.channel.send(`🚫 Removed <@${userId}> from the queue.`);
  }

  if (cmd === "!cancelmatch") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    // Get the match for this specific channel
    const match = matches.get(message.channel.id);
    if (!match) {
      return message.reply("❌ There is no active match in this channel to cancel.");
    }

    const { matchChannel, team1VC, team2VC, matchCategory } = match;
    const guild = message.guild;

    try {
      // Delete all match-related channels if they still exist
      if (matchChannel) await matchChannel.delete().catch(() => {});
      if (team1VC) await team1VC.delete().catch(() => {});
      if (team2VC) await team2VC.delete().catch(() => {});
      if (matchCategory) await matchCategory.delete().catch(() => {});

      // Remove this match from active matches
      matches.delete(message.channel.id);

      await message.channel.send("🛑 The current match has been canceled and all match channels have been deleted.");
    } catch (err) {
      console.error("Error canceling match:", err);
      await message.channel.send("⚠️ Failed to fully cancel the match. Check console for details.");
    }
  }

  if (cmd === "!simulate") {
    if (!message.member.permissions.has("ManageGuild")) {
        return message.reply("❌ Only staff members can use this command.");
    }

    const count = parseInt(args[0] || "10");
    
    // Get registered players with complete role preferences
    const eligiblePlayers = Object.keys(playerData).filter(id => {
        // Filter out system keys
        if (id.startsWith('_')) return false;
        
        const player = playerData[id];
        
        // Check for summoner name and complete role preferences
        if (!player?.summonerName) return false;
        
        // Enhanced role verification: must have exactly 5 roles, all non-null
        if (!player.roles || player.roles.length !== 5 || player.roles.some(role => !role)) {
            return false;
        }
        
        return true;
    });

    if (eligiblePlayers.length === 0) {
        return message.reply("❌ No registered players with complete role preferences (all 5 positions set) found.");
    }

    // Clear current queue first
    queue = [];
    
    // Shuffle eligible players array to get random selection
    const shuffledPlayers = [...eligiblePlayers].sort(() => Math.random() - 0.5);
    
    // Add random players to queue (up to the requested count)
    const playersToAdd = Math.min(count, shuffledPlayers.length);
    let addedCount = 0;
    let skippedCount = 0;

    for (let i = 0; i < playersToAdd; i++) {
        const playerId = shuffledPlayers[i];
        
        // Additional safety check
        const player = playerData[playerId];
        if (player.roles && player.roles.length === 5 && !player.roles.some(role => !role)) {
            if (!queue.includes(playerId)) {
                queue.push(playerId);
                addedCount++;
            }
        } else {
            skippedCount++;
        }
    }

    saveData();
    
    let response = `🤖 Randomly added ${addedCount} players with complete role preferences to queue. Queue = ${queue.length}/${QUEUE_SIZE}`;
    
    // Provide feedback on skipped players
    if (skippedCount > 0) {
        response += `\n⚠️ ${skippedCount} players skipped due to incomplete role preferences.`;
    }
    
    if (addedCount < count) {
        response += `\nℹ️ Only ${eligiblePlayers.length} players with complete role preferences available.`;
    }

    // Show which players were added
    const addedPlayerMentions = queue.map(id => `<@${id}>`).join(', ');
    response += `\n\n**Players added:** ${addedPlayerMentions}`;
    
    message.channel.send(response);
    await updateQueueMessage();

    // ADD SOLUTION 3: Strict Ready Check Trigger
    if (queue.length === QUEUE_SIZE && !activeReadyCheck) {
        await startReadyCheck(message.channel);
    }
  }

  // In your messageCreate handler, update the !endmatch command:
  if (cmd === "!endmatch") {
    // Only allow staff (ManageGuild permission) to run this command
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }
    
    const team = args[0];
    if (!team || (team !== "1" && team !== "2")) {
      return message.reply("Usage: !endmatch <1|2>");
    }
    
    // This will now use the channel-specific match
    endMatch(message.channel, team);
  }

  if (cmd === "!clearqueue") {
  // Only staff members
  if (!message.member.permissions.has("ManageGuild")) {
    return message.reply("❌ Only staff members can use this command.");
  }

  if (queue.length === 0) {
    return message.reply("⚠️ The queue is already empty.");
  }

  queue = [];
  saveData();
  await updateQueueMessage();
  message.channel.send("🧹 The queue has been cleared.");
  }

  if (cmd === "!togglequeue") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    queueEnabled = !queueEnabled;
    message.channel.send(`🔘 Queue is now **${queueEnabled ? "OPEN" : "CLOSED"}**.`);

    // Optional: notify users if queue just closed
    if (!queueEnabled) {
      await updateQueueMessage(); // Update the queue message with current status
    }
  }

  // ---------------- !forceregister ----------------
  if (message.content.startsWith("!forceregister")) {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ You need Manage Server permissions to do that.");
    }
    
    const args = message.content.split(" ");
    const userMention = args[1];
    const url = args[2];
    
    if (!userMention || !url) {
      return message.reply("Usage: !forceregister <@user> <OP.GG link> [rank division lp]\nExample: !forceregister @user https://op.gg/summoners/na/example\nExample with rank: !forceregister @user https://op.gg/summoners/na/example Gold 3 75");
    }
    
    if (!url.includes("op.gg")) return message.reply("❌ Please provide a valid OP.GG link.");
    
    const userId = userMention.replace(/[<@!>]/g, "");
    if (!userId) return message.reply("❌ Invalid user mention");

    try {
      // Check if custom rank parameters are provided
      const hasCustomRank = args.length >= 5; // URL + rank + division + lp
      
      let rank, division, lp;
      
      if (hasCustomRank) {
        // Use custom rank provided by staff
        rank = args[3].charAt(0).toUpperCase() + args[3].slice(1).toLowerCase();
        const divText = args[4].toUpperCase();
        
        // Handle division (can be number or roman numeral)
        const romanToNumber = { IV: 4, III: 3, II: 2, I: 1 };
        division = !isNaN(parseInt(divText)) ? parseInt(divText) : romanToNumber[divText];
        
        lp = parseInt(args[5]) || 0;
        
        // Validate rank
        const validRanks = ["Iron", "Bronze", "Silver", "Gold", "Platinum", "Emerald", "Diamond", "Master", "Grandmaster", "Challenger"];
        if (!validRanks.includes(rank)) {
          return message.reply(`❌ Invalid rank. Valid ranks are: ${validRanks.join(", ")}`);
        }
        
        // Validate division for non-Master+ ranks
        if (["Iron", "Bronze", "Silver", "Gold", "Platinum", "Emerald", "Diamond"].includes(rank)) {
          if (!division || division < 1 || division > 4) {
            return message.reply("❌ Invalid division. Must be between 1-4 for ranks up to Diamond.");
          }
        } else {
          // Master+ ranks don't have divisions
          division = null;
        }
        
        // Validate LP
        if (lp < 0 || lp > 999) {
          return message.reply("❌ Invalid LP. Must be between 0-999.");
        }
        
      } else {
        // Try to scrape rank from OP.GG
        const res = await axios.get(url);
        const $ = cheerio.load(res.data);
        const tierText = $("strong.text-xl").first().text().trim();
        const lpText = $("span.text-xs.text-gray-500").first().text().trim();
        const lp = parseInt(lpText);
        
        if (!tierText || isNaN(lp)) {
          return message.reply("❌ Could not parse rank/LP from OP.GG. Please provide rank manually: !forceregister <@user> <OP.GG link> <rank> <division> <lp>");
        }
        
        const tierParts = tierText.trim().split(/\s+/);
        if (tierParts.length === 2) {
          rank = tierParts[0].charAt(0).toUpperCase() + tierParts[0].slice(1).toLowerCase();
          const divText = tierParts[1].toUpperCase();
          const romanToNumber = { IV: 4, III: 3, II: 2, I: 1 };
          division = !isNaN(parseInt(divText)) ? parseInt(divText) : romanToNumber[divText] || 4;
        } else {
          rank = tierParts[0].charAt(0).toUpperCase() + tierParts[0].slice(1).toLowerCase();
          division = null;
        }
      }
      
      ensurePlayer(userId);
      playerData[userId].summonerName = url;
      playerData[userId].rank = rank;
      playerData[userId].division = division;
      playerData[userId].lp = lp;
      playerData[userId].IHP = getIHP(playerData[userId]);
      
      saveData();
      await updateLeaderboardChannel(message.guild);
      
      const rankDisplay = division ? `${rank} ${division} ${lp} LP` : `${rank} ${lp} LP`;
      return message.reply(`✅ Force-registered <@${userId}> as **${rankDisplay}**${hasCustomRank ? " (manual rank)" : ""}`);
      
    } catch (err) {
      console.error(err);
      
      // If scraping fails but custom rank wasn't provided, show usage
      if (args.length < 5) {
        return message.reply(`❌ Failed to fetch OP.GG page and no manual rank provided.\nUsage: !forceregister <@user> <OP.GG link> [rank division lp]\nExample with rank: !forceregister @user https://op.gg/summoners/na/example Gold 3 75`);
      } else {
        return message.reply("❌ Failed to process registration. Make sure the OP.GG link is correct.");
      }
    }
  }

  if (cmd === "!changewinner") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    if (args.length < 2) {
      return message.reply("Usage: !changewinner <match_id> <1|2>\nUse !recentmatches to find match IDs");
    }

    const matchId = args[0];
    const newWinner = args[1];
    
    if (newWinner !== "1" && newWinner !== "2") {
      return message.reply("❌ Winner must be either '1' (Team 1) or '2' (Team 2)");
    }

    // Load match history
    const matchHistory = loadMatchHistory();
    const matchRecord = matchHistory.find(match => match.id === matchId);
    
    if (!matchRecord) {
      return message.reply("❌ Match not found. Use !recentmatches to see available matches.");
    }

    if (matchRecord.voided) {
      return message.reply("❌ This match has been voided and cannot be modified.");
    }

    // Store original state for reversal
    const originalState = {
      winner: matchRecord.winner,
      eloChanges: JSON.parse(JSON.stringify(matchRecord.eloChanges))
    };

    // Reverse original ELO changes
    originalState.eloChanges.forEach(change => {
      const player = ensurePlayer(change.id);
      player.wins -= change.isWinner ? 1 : 0;
      player.losses -= change.isWinner ? 0 : 1;
      
      // Reverse ELO change
      const currentIHP = getIHP(player);
      const reversedIHP = currentIHP - change.change;
      const newStats = IHPToRank(reversedIHP);
      Object.assign(player, newStats);
    });

    // Apply new winner ELO changes
    const newWinners = newWinner === "1" ? matchRecord.team1 : matchRecord.team2;
    const newLosers = newWinner === "1" ? matchRecord.team2 : matchRecord.team1;

    const newEloChanges = [];

    // Update new winners
    newWinners.forEach(id => {
      const p = ensurePlayer(id);
      const oldIHP = getIHP(p);
      
      p.wins++;
      p.lp += 20;

      const newIHP = getIHP(p);
      const newStats = IHPToRank(newIHP);
      Object.assign(p, newStats);

      newEloChanges.push({
        id,
        oldIHP,
        newIHP,
        change: newIHP - oldIHP,
        isWinner: true
      });
    });

    // Update new losers
    newLosers.forEach(id => {
      const p = ensurePlayer(id);
      const oldIHP = getIHP(p);
      
      p.losses++;
      p.lp -= 20;

      const newIHP = getIHP(p);
      const newStats = IHPToRank(newIHP);
      Object.assign(p, newStats);

      newEloChanges.push({
        id,
        oldIHP,
        newIHP,
        change: newIHP - oldIHP,
        isWinner: false
      });
    });

    // Update match record
    matchRecord.winner = newWinner;
    matchRecord.eloChanges = newEloChanges;
    saveMatchHistory(matchHistory);
    saveData();

    // Update leaderboard
    await updateLeaderboardChannel(message.guild);

    const embed = new EmbedBuilder()
      .setTitle("✅ Match Winner Updated")
      .setDescription(`Match ${matchId} winner changed to Team ${newWinner}`)
      .addFields(
        { name: "Previous Winner", value: `Team ${originalState.winner}`, inline: true },
        { name: "New Winner", value: `Team ${newWinner}`, inline: true },
        { name: "ELO Adjustments", value: "All player ELO, wins, and losses have been updated accordingly" }
      )
      .setColor(0x00ff00)
      .setTimestamp();

    await message.channel.send({ embeds: [embed] });
  }

  // Add this to your COMMANDS section
  if (cmd === "!voidmatch") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    if (args.length < 1) {
      return message.reply("Usage: !voidmatch <match_id>\nUse !recentmatches to find match IDs");
    }

    const matchId = args[0];

    // Load match history
    const matchHistory = loadMatchHistory();
    const matchRecord = matchHistory.find(match => match.id === matchId);
    
    if (!matchRecord) {
      return message.reply("❌ Match not found. Use !recentmatches to see available matches.");
    }

    if (matchRecord.voided) {
      return message.reply("❌ This match is already voided.");
    }

    // Reverse all ELO changes
    matchRecord.eloChanges.forEach(change => {
      const player = ensurePlayer(change.id);
      
      // Reverse win/loss stats
      player.wins -= change.isWinner ? 1 : 0;
      player.losses -= change.isWinner ? 0 : 1;
      
      // Reverse ELO change
      const currentIHP = getIHP(player);
      const reversedIHP = currentIHP - change.change;
      const newStats = IHPToRank(reversedIHP);
      Object.assign(player, newStats);
    });

    // Mark match as voided
    matchRecord.voided = true;
    matchRecord.voidedAt = Date.now();
    matchRecord.voidedBy = message.author.id;
    saveMatchHistory(matchHistory);
    saveData();

    // Update leaderboard
    await updateLeaderboardChannel(message.guild);

    const embed = new EmbedBuilder()
      .setTitle("✅ Match Voided")
      .setDescription(`Match ${matchId} has been voided and all ELO changes reversed`)
      .addFields(
        { name: "Original Winner", value: `Team ${matchRecord.winner}`, inline: true },
        { name: "Voided By", value: `<@${message.author.id}>`, inline: true },
        { name: "Stats Reversed", value: "All ELO, wins, and losses have been reset to pre-match values" }
      )
      .setColor(0xffa500)
      .setTimestamp();

    await message.channel.send({ embeds: [embed] });
  }

  // Add this to your COMMANDS section
  if (cmd === "!recentmatches") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    const matchHistory = loadMatchHistory();
    const recentMatches = matchHistory.slice(-10).reverse(); // Get 10 most recent matches

    if (recentMatches.length === 0) {
      return message.reply("❌ No match history found.");
    }

    const matchList = recentMatches.map(match => {
      const date = new Date(match.timestamp).toLocaleDateString();
      const status = match.voided ? "❌ VOIDED" : "✅ ACTIVE";
      return `**${match.id}** - ${date} - Team ${match.winner} won - ${status}`;
    }).join('\n');

    const embed = new EmbedBuilder()
      .setTitle("📜 Recent Matches")
      .setDescription(matchList)
      .setFooter({ text: "Use !changewinner <match_id> <1|2> or !voidmatch <match_id>" })
      .setColor(0x3498db)
      .setTimestamp();

    await message.channel.send({ embeds: [embed] });
  }

  // Add this to your COMMANDS section
  if (cmd === "!unvoidmatch") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    if (args.length < 1) {
      return message.reply("Usage: !unvoidmatch <match_id>");
    }

    const matchId = args[0];

    const matchHistory = loadMatchHistory();
    const matchRecord = matchHistory.find(match => match.id === matchId);
    
    if (!matchRecord) {
      return message.reply("❌ Match not found.");
    }

    if (!matchRecord.voided) {
      return message.reply("❌ This match is not voided.");
    }

    // Re-apply original ELO changes
    matchRecord.eloChanges.forEach(change => {
      const player = ensurePlayer(change.id);
      
      // Re-apply win/loss stats
      player.wins += change.isWinner ? 1 : 0;
      player.losses += change.isWinner ? 0 : 1;
      
      // Re-apply ELO change
      const currentIHP = getIHP(player);
      const revertedIHP = currentIHP + change.change;
      const newStats = IHPToRank(revertedIHP);
      Object.assign(player, newStats);
    });

    // Mark match as active again
    matchRecord.voided = false;
    delete matchRecord.voidedAt;
    delete matchRecord.voidedBy;
    saveMatchHistory(matchHistory);
    saveData();

    await updateLeaderboardChannel(message.guild);

    const embed = new EmbedBuilder()
      .setTitle("✅ Match Restored")
      .setDescription(`Match ${matchId} has been restored and all ELO changes re-applied`)
      .addFields(
        { name: "Winner", value: `Team ${matchRecord.winner}`, inline: true },
        { name: "Restored By", value: `<@${message.author.id}>`, inline: true }
      )
      .setColor(0x00ff00)
      .setTimestamp();

    await message.channel.send({ embeds: [embed] });
  }
});

// ---------------- MATCHMAKING WITH ROLE ASSIGNMENT ----------------
async function makeTeams(channel) {
  trackRequest();
  // Filter out any players with block conflicts in the current queue
  const playersWithBlockConflicts = new Set();
  
  for (const playerId of queue) {
    const conflicts = checkQueueForBlocks(playerId);
    if (conflicts.length > 0) {
      playersWithBlockConflicts.add(playerId);
      // Also add the players they conflict with
      conflicts.forEach(conflictId => playersWithBlockConflicts.add(conflictId));
    }
  }
  
  if (playersWithBlockConflicts.size > 0) {
    const conflictList = Array.from(playersWithBlockConflicts).map(id => `<@${id}>`).join(', ');
    await channel.send({
      content: `🚫 **Block Conflicts Detected**\nThe following players have block conflicts and cannot be in the same match:\n${conflictList}\n\nPlease resolve these conflicts before queuing together.`
    });
    
    // Remove all conflicting players from queue
    queue = queue.filter(id => !playersWithBlockConflicts.has(id));
    saveData();
    await updateQueueMessage();
    return;
  }

  const players = [...queue];
  
  // ADDED: Exhaustive combination search for best ELO balance
  let bestTeam1 = null;
  let bestTeam2 = null;
  let bestDiff = Infinity;
  let bestAvg1 = 0;
  let bestAvg2 = 0;

  // Generate all possible combinations of 5 players for team 1
  // The remaining 5 players will automatically form team 2
  function generateCombinations(arr, k) {
    const result = [];
    
    function backtrack(start, current) {
      if (current.length === k) {
        result.push([...current]);
        return;
      }
      
      for (let i = start; i < arr.length; i++) {
        current.push(arr[i]);
        backtrack(i + 1, current);
        current.pop();
      }
    }
    
    backtrack(0, []);
    return result;
  }

  console.log(`🔍 Starting exhaustive team combination search for ${players.length} players`);
  
  // Generate all possible team combinations
  const allTeam1Combinations = generateCombinations(players, 5);
  
  console.log(`📊 Evaluating ${allTeam1Combinations.length} possible team combinations`);
  
  // Evaluate each combination
  for (const team1 of allTeam1Combinations) {
    const team2 = players.filter(player => !team1.includes(player));
    
    // Calculate average ELO for both teams
    const sum1 = team1.reduce((sum, id) => sum + getIHP(ensurePlayer(id)), 0);
    const sum2 = team2.reduce((sum, id) => sum + getIHP(ensurePlayer(id)), 0);
    const avg1 = sum1 / 5;
    const avg2 = sum2 / 5;
    const diff = Math.abs(avg1 - avg2);
    
    // Update best combination if this one is better
    if (diff < bestDiff) {
      bestDiff = diff;
      bestTeam1 = team1;
      bestTeam2 = team2;
      bestAvg1 = avg1;
      bestAvg2 = avg2;
    }
    
    // Early exit if we find a perfect balance
    if (bestDiff === 0) break;
  }

  console.log(`✅ Best team combination found with ELO difference: ${bestDiff.toFixed(2)}`);
  console.log(`🔵 Team 1 Avg ELO: ${bestAvg1.toFixed(2)}, 🔴 Team 2 Avg ELO: ${bestAvg2.toFixed(2)}`);

  // ---------------- OPTIMIZED ROLE ASSIGNMENT (MINIMIZE PREFERENCE POINTS) ----------------
  function assignRoles(team) {
    const roleSlots = ["Top", "Jungle", "Mid", "Bot", "Support"];
    const assigned = {};
    
    // Get all possible role assignments for this team
    const allAssignments = generateAllRoleAssignments(team, roleSlots);
    
    if (allAssignments.length === 0) {
      // Fallback: assign randomly if no valid assignments found
      return assignRolesFallback(team, roleSlots);
    }
    
    // Find the assignment with the lowest total preference points
    let bestAssignment = null;
    let bestTotalPoints = Infinity;
    let bestEloSum = -Infinity; // For tie-breaking (higher Elo gets preference)
    
    for (const assignment of allAssignments) {
      const { totalPoints, eloSum } = calculateAssignmentQuality(team, assignment);
      
      // Prefer lower total points, and if tied, prefer higher Elo sum
      if (totalPoints < bestTotalPoints || 
          (totalPoints === bestTotalPoints && eloSum > bestEloSum)) {
        bestTotalPoints = totalPoints;
        bestEloSum = eloSum;
        bestAssignment = assignment;
      }
    }
    
    return bestAssignment || assignRolesFallback(team, roleSlots);
  }

  function generateAllRoleAssignments(team, roleSlots) {
    const assignments = [];
    
    // Recursive function to generate all valid role assignments
    function generate(currentAssignment, usedRoles, playerIndex) {
      if (playerIndex === team.length) {
        assignments.push({ ...currentAssignment });
        return;
      }
      
      const playerId = team[playerIndex];
      const playerRoles = playerData[playerId].roles || [];
      
      // Try each possible role for this player
      for (const role of roleSlots) {
        if (!usedRoles.has(role)) {
          // Check if player can play this role (either specific preference OR Fill)
          const roleIndex = playerRoles.indexOf(role);
          const hasFill = playerRoles.includes("Fill");
          
          if (roleIndex !== -1 || hasFill) {
            currentAssignment[playerId] = role;
            usedRoles.add(role);
            
            generate(currentAssignment, usedRoles, playerIndex + 1);
            
            // Backtrack
            delete currentAssignment[playerId];
            usedRoles.delete(role);
          }
        }
      }
    }
    
    generate({}, new Set(), 0);
    return assignments;
  }

  function calculateAssignmentQuality(team, assignment) {
    let totalPoints = 0;
    let eloSum = 0;
    
    for (const playerId of team) {
      const role = assignment[playerId];
      const playerRoles = playerData[playerId].roles || [];
      const roleIndex = playerRoles.indexOf(role);
      
      // Calculate preference points
      if (roleIndex !== -1) {
        // Specific role preference: 1st pref = 1 point, 2nd = 2 points, etc.
        totalPoints += roleIndex + 1;
      } else if (playerRoles.includes("Fill")) {
        // Fill gets points based on where Fill appears in their preferences
        const fillIndex = playerRoles.indexOf("Fill");
        totalPoints += fillIndex + 1; // Fill at position 1 = 1 point, position 2 = 2 points, etc.
      } else {
        // Unwanted role gets maximum penalty
        totalPoints += 6; // Higher than any preference
      }
      
      // Sum Elo for tie-breaking
      eloSum += getIHP(ensurePlayer(playerId));
    }
    
    return { totalPoints, eloSum };
  }

  function calculateTeamSatisfaction(team, roles) {
    let totalPoints = 0;
    let perfectAssignments = 0;
    let goodAssignments = 0;
    
    for (const playerId of team) {
      const role = roles[playerId];
      const playerRoles = playerData[playerId].roles || [];
      const preferenceIndex = playerRoles.indexOf(role);
      
      if (preferenceIndex === 0) {
        perfectAssignments++;
        totalPoints += 1;
      } else if (preferenceIndex === 1) {
        goodAssignments++;
        totalPoints += 2;
      } else if (preferenceIndex >= 2 && preferenceIndex <= 4) {
        totalPoints += preferenceIndex + 1;
      } else if (playerRoles.includes("Fill")) {
        const fillIndex = playerRoles.indexOf("Fill");
        totalPoints += fillIndex + 1; // Fill at position 1 = 1 point, position 2 = 2 points, etc.
      } else {
        totalPoints += 6; // Unwanted role penalty
      }
    }
    
    return { totalPoints, perfectAssignments, goodAssignments };
  }

  function assignRolesFallback(team, roleSlots) {
    // Simple fallback assignment when no optimal solution found
    const assigned = {};
    const availableRoles = [...roleSlots];
    
    for (const playerId of team) {
      const playerRoles = playerData[playerId].roles || [];
      
      // Try to find a preferred role
      let assignedRole = null;
      for (const role of availableRoles) {
        if (playerRoles.includes(role)) {
          assignedRole = role;
          break;
        }
      }
      
      // If no preferred role, use Fill or any available role
      if (!assignedRole && playerRoles.includes("Fill")) {
        assignedRole = availableRoles[0];
      }
      
      // Last resort: assign any role
      if (!assignedRole) {
        assignedRole = availableRoles[0];
      }
      
      assigned[playerId] = assignedRole;
      availableRoles.splice(availableRoles.indexOf(assignedRole), 1);
    }
    
    return assigned;
  }

  // Now assign roles to both teams
  const team1Roles = assignRoles(bestTeam1);
  const team2Roles = assignRoles(bestTeam2);

  // Calculate role assignment quality
  const team1Satisfaction = calculateTeamSatisfaction(bestTeam1, team1Roles);
  const team2Satisfaction = calculateTeamSatisfaction(bestTeam2, team2Roles);

  logRoleAssignmentToConsole(bestTeam1, bestTeam2, team1Roles, team2Roles, team1Satisfaction, team2Satisfaction);

  const avg1 = Math.round(bestTeam1.reduce((a, id) => a + getIHP(ensurePlayer(id)), 0) / 5);
  const avg2 = Math.round(bestTeam2.reduce((a, id) => a + getIHP(ensurePlayer(id)), 0) / 5);

  // Sort teams by Elo descending
  const team1Sorted = [...bestTeam1].sort((a,b) => getIHP(ensurePlayer(b)) - getIHP(ensurePlayer(a)));
  const team2Sorted = [...bestTeam2].sort((a,b) => getIHP(ensurePlayer(b)) - getIHP(ensurePlayer(a)));

  // Store highest Elo player ID per team
  const team1TopElo = team1Sorted[0];
  const team2TopElo = team2Sorted[0];

  // ---------------- CREATE SEPARATE MATCH CATEGORY FOR EACH MATCH ----------------
  const guild = channel.guild;
  
  // Add a lock for match ID generation
  let matchIdLock = false;

  async function getNextMatchId() {
    // Wait for lock if another match is being created
    while (matchIdLock) {
      await new Promise(resolve => setTimeout(resolve, 100));
    }
    
    try {
      matchIdLock = true;
      
      const matchHistory = await loadMatchHistory();
      
      // If no matches exist, start from 1
      if (matchHistory.length === 0) {
        return "1";
      }
      
      // Find the highest existing match ID and increment
      const maxId = Math.max(...matchHistory.map(match => {
        // Handle both string and number IDs
        const id = match.id;
        return typeof id === 'string' ? parseInt(id) || 0 : id;
      }).filter(id => !isNaN(id)));
      
      return (maxId + 1).toString();
      
    } finally {
      // Always release the lock
      matchIdLock = false;
    }
  }

  const matchId = await getNextMatchId();
  const matchCategoryName = `Match ${matchId}`; // Simpler name without timestamp
  
  // Create a dedicated category for this match
  const matchCategory = await guild.channels.create({ 
    name: matchCategoryName, 
    type: 4, // Category type
    permissionOverwrites: [
      {
        id: guild.id, // @everyone
        allow: ['ViewChannel'] // CHANGE: Allow everyone to view instead of deny
      }
    ]
  });

  // Create match text channel - MAKE PRIVATE
  const matchChannel = await guild.channels.create({ 
    name: "match-lobby", 
    type: 0, 
    parent: matchCategory.id,
    permissionOverwrites: [
      {
        id: guild.id, // @everyone
        deny: ['ViewChannel'] // CHANGE: Deny view for everyone
      },
      // Allow match participants to view and send messages
      ...bestTeam1.map(playerId => ({
        id: playerId,
        type: 1,
        allow: [/*'ViewChannel',*/ 'SendMessages', 'ReadMessageHistory'],
        deny: ['ViewChannel']
      })),
      ...bestTeam2.map(playerId => ({
        id: playerId,
        type: 1,
        allow: [/*'ViewChannel'*/, 'SendMessages', 'ReadMessageHistory'],
        deny: ['ViewChannel']
      }))
    ]
  });

  // Create team voice channels with proper permissions - UPDATED VERSION
  const team1VC = await guild.channels.create({ 
    name: "🔵 Team 1 (Blue)", 
    type: 2, 
    parent: matchCategory.id,
    permissionOverwrites: [
      {
        id: guild.id, // @everyone
        allow: ['ViewChannel', 'Connect'], // Everyone can see the channel
        deny: ['Speak'], // Mute spectators/other team
      },
      ...bestTeam1.map(playerId => ({
        id: playerId,
        type: 1,
        allow: ['ViewChannel', 'Connect', 'Speak']
      }))
    ]
  });

  const team2VC = await guild.channels.create({ 
    name: "🔴 Team 2 (Red)", 
    type: 2, 
    parent: matchCategory.id,
    permissionOverwrites: [
      {
        id: guild.id, // @everyone
        allow: ['ViewChannel', 'Connect'], // Everyone can see the channel
        deny: ['Speak'], // Mute spectators/other team
      },
      ...bestTeam2.map(playerId => ({
        id: playerId,
        type: 1,
        allow: ['ViewChannel', 'Connect', 'Speak']
      }))
    ]
  });

  // --- Build Multi OP.GG Links for each team ---
  const buildMulti = (team) => {
    const summoners = team
      .map((id) => playerData[id]?.summonerName)
      .filter(Boolean)
      .map((url) => {
        try {
          const parts = url.split("/");
          const namePart = decodeURIComponent(parts[parts.length - 1]);
          return namePart.replace("-", "%23").replace(/\s+/g, "+");
        } catch {
          return null;
        }
      })
      .filter(Boolean);
    if (summoners.length === 0) return "https://www.op.gg/";
    return `https://www.op.gg/lol/multisearch/na?summoners=${summoners.join("%2C")}`;
  };

  const team1Link = buildMulti(bestTeam1);
  const team2Link = buildMulti(bestTeam2);

  // --- Sort players by role for embed display with rank, LP, IHP, and emoji ---
  const roleEmojis = { Top: "<:TopLane:1426322701085184052>", Jungle: "<:Jungle:1426322644067946576>", Mid: "<:MidLane:1426322657820807248>", Bot: "<:ADC:1426322671045709986>", Support: "<:Support:1426322683603325029>" };
  const roleOrder = { Top: 1, Jungle: 2, Mid: 3, Bot: 4, Support: 5 };

  
  function formatTeamDisplay(team, roles) {
    return team
      .map((id) => {
        const player = playerData[id];
        const rank = player?.rank || "Unranked";
        const division = player?.division;
        const lp = player?.lp ?? 0;
        const ihp = getIHP(ensurePlayer(id)) ?? 0;
        const role = roles[id];
        
        // FIX: Handle null division for Master+ ranks
        const divisionDisplay = division ? ` ${division}` : '';
        
        return {
          display: `<@${id}> / ${rank}${divisionDisplay} ${lp} LP (${ihp}) / ${roleEmojis[role]} ${role}`,
          role,
        };
      })
      .sort((a, b) => roleOrder[a.role] - roleOrder[b.role])
      .map((p) => p.display)
      .join("\n");
  }

  // --- Create Draft Lobby using draftlol.dawe.gg ---
  let blue = "", red = "", spectator = "", lobbyUrl = "";

  try {
    const links = await createDraftLolLobby();
    blue = links.blue;
    red = links.red;
    spectator = links.spectator;
    lobbyUrl = links.lobby; // The 4-part URL to create the lobby
    
    console.log(`✅ Generated 4-part lobby URL: ${lobbyUrl}`);
  } catch (err) {
    console.error("Failed to generate draft links:", err);
    // Continue without draft links
  }

    const lobbyRow = new ActionRowBuilder().addComponents(
    new ButtonBuilder()
      .setLabel('🎮 CREATE LOBBY (Click This First!)')
      .setStyle(ButtonStyle.Link)
      .setURL(lobbyUrl)
  );

  const teamRow = new ActionRowBuilder().addComponents(
    new ButtonBuilder()
      .setLabel('🟦 Blue Team Draft')
      .setStyle(ButtonStyle.Link)
      .setURL(blue),
    new ButtonBuilder()
      .setLabel('🔴 Red Team Draft')
      .setStyle(ButtonStyle.Link)
      .setURL(red),
    new ButtonBuilder()
      .setLabel('👁️ Spectator View')
      .setStyle(ButtonStyle.Link)
      .setURL(spectator)
  );

  const managementRow = new ActionRowBuilder().addComponents(
    new ButtonBuilder()
      .setCustomId(`report_win_1`)
      .setLabel('🏆 Team 1 Won')
      .setStyle(ButtonStyle.Success),
    new ButtonBuilder()
      .setCustomId(`report_win_2`)
      .setLabel('🏆 Team 2 Won')
      .setStyle(ButtonStyle.Success)
  );

  // In the matchEmbed, add the lobby URL information:
  const matchEmbed = new EmbedBuilder()
  .setTitle("🎮 Match Lobby")
  .setDescription(`**IMPORTANT: Follow these steps to set up the draft:**

  **Step 1: Create the Lobby**
  🔗 **[Click here to CREATE the draft lobby](${lobbyUrl})**
  → This must be done by **ONE person** (any player or staff)
  → Just open the link and close the tab - the lobby will be created

  **Step 2: Join Your Team**
  After the lobby is created, use these links:

  🟦 **Blue Team:** [Join Blue Draft](${blue})
  🔴 **Red Team:** [Join Red Draft](${red})  
  👁️ **Spectators:** [Spectator Link](${spectator})

  **Troubleshooting:**
  - If you see a blank screen, wait 30 seconds and refresh
  - Make sure Step 1 was completed first
  - If issues persist, use the manual draft links below

  **Manual Setup (if automated fails):**
  1. Visit: draftlol.dawe.gg
  2. Create a new draft manually
  3. Share the links with your team`)
  .addFields(
    {
      name: `🔵 Team 1 (Avg Elo: ${Math.round(bestAvg1)})`,
      value: formatTeamDisplay(bestTeam1, team1Roles),
      inline: false,
    },
    {
      name: `🔴 Team 2 (Avg Elo: ${Math.round(bestAvg2)})`,
      value: formatTeamDisplay(bestTeam2, team2Roles),
      inline: false,
    }
  )
  .setColor(0x00ff00);


  // Send with all rows
  const messageOptions = {
    embeds: [matchEmbed],
    components: [lobbyRow, teamRow, managementRow]
  };

  // Only add content if draft links failed
  if (!blue || !red || !spectator) {
    messageOptions.content = `❌ Failed to create draft lobby. Players will need to make draft manually.`;
  }

  const matchData = {
    team1: bestTeam1,
    team2: bestTeam2,
    matchChannel,
    matchCategory,
    team1VC,
    team2VC,
    team1Roles,
    team2Roles,
    blue, 
    red, 
    spectator,
    matchId: matchId, // Store the match ID
    matchMessageId: null,
    votes: {
      team1: new Set(), // Players who voted for team 1
      team2: new Set()  // Players who voted for team 2
    }
  };

  // Send the message
  const matchMessage = await matchChannel.send(messageOptions);

  // Store the match message ID for later reference
  matchData.matchMessageId = matchMessage.id;

  // Store match by channel ID
  matches.set(matchChannel.id, matchData);

  queue = [];
  saveData();
  updateQueueMessage();
}


// ---------------- END MATCH ----------------
async function endMatch(channel, winner, isVoided = false) {
  // Get the match for this specific channel
  const match = matches.get(channel.id);
  if (!match) {
    return channel.send("❌ No active match found in this channel.");
  }

  const { team1, team2, matchChannel, matchCategory, team1VC, team2VC, matchId } = match;
  const guild = channel.guild;

  let historyChannel = guild.channels.cache.find(c => c.name === "match-history" && c.type === 0);
  if (!historyChannel) {
    historyChannel = await guild.channels.create({ name: "match-history", type: 0 });
  }

  const generalChannel = guild.channels.cache.find(c => c.name === "general" && c.type === 0);

  const winners = winner === "1" ? team1 : team2;
  const losers = winner === "1" ? team2 : team1;

  // Track ELO changes and rank changes
  const eloChanges = [];
  const rankChanges = [];

  // Update winners and track changes
  winners.forEach((id) => {
    const p = ensurePlayer(id);
    const oldIHP = getIHP(p);
    const oldRank = p.rank;
    const oldDivision = p.division;
    const oldLP = p.lp;

    p.wins++;
    p.lp += 20;

    const newIHP = getIHP(p);
    const newStats = IHPToRank(newIHP);
    Object.assign(p, newStats);

    // Track ELO change
    eloChanges.push({
      id,
      oldIHP,
      newIHP,
      change: newIHP - oldIHP,
      isWinner: true,
      oldRank,
      oldDivision,
      oldLP,
      newRank: p.rank,
      newDivision: p.division,
      newLP: p.lp
    });

    // Check for rank changes
    if (p.rank !== oldRank || p.division !== oldDivision) {
      rankChanges.push({
        id,
        oldRank,
        oldDivision,
        newRank: p.rank,
        newDivision: p.division,
        isPromotion: newIHP > oldIHP
      });
    }
  });

  // Update losers and track changes
  losers.forEach((id) => {
    const p = ensurePlayer(id);
    const oldIHP = getIHP(p);
    const oldRank = p.rank;
    const oldDivision = p.division;
    const oldLP = p.lp;

    p.losses++;
    p.lp -= 20;

    const newIHP = getIHP(p);
    const newStats = IHPToRank(newIHP);
    Object.assign(p, newStats);

    // Track ELO change
    eloChanges.push({
      id,
      oldIHP,
      newIHP,
      change: newIHP - oldIHP,
      isWinner: false,
      oldRank,
      oldDivision,
      oldLP,
      newRank: p.rank,
      newDivision: p.division,
      newLP: p.lp
    });

    // Check for rank changes
    if (p.rank !== oldRank || p.division !== oldDivision) {
      rankChanges.push({
        id,
        oldRank,
        oldDivision,
        newRank: p.rank,
        newDivision: p.division,
        isPromotion: newIHP > oldIHP
      });
    }
  });

  const matchHistory = await loadMatchHistory();
  const matchRecord = {
    id: matchId, // Use the sequential ID instead of channel ID
    timestamp: Date.now(),
    team1: team1,
    team2: team2,
    winner: winner,
    eloChanges: eloChanges.map(change => ({
      id: change.id,
      oldIHP: change.oldIHP,
      newIHP: change.newIHP,
      change: change.change,
      isWinner: change.isWinner
    })),
    voided: isVoided
  };
  
  matchHistory.push(matchRecord);
  await saveMatchHistory(matchHistory);

  saveData();

  // Create enhanced history embed with ELO changes - NOW INCLUDES MATCH ID
  const team1Players = team1.map(id => `<@${id}>`).join(", ") || "—";
  const team2Players = team2.map(id => `<@${id}>`).join(", ") || "—";

  // Build ELO changes display
  const eloChangesText = eloChanges.map(change => {
    const changeSymbol = change.change >= 0 ? "🟢" : "🔴";
    const changeText = change.change >= 0 ? `+${change.change}` : `${change.change}`;
    const winLoss = change.isWinner ? "🏆" : "💀";
    
    const oldRankDisplay = change.oldDivision ? `${change.oldRank} ${change.oldDivision}` : change.oldRank;
    const newRankDisplay = change.newDivision ? `${change.newRank} ${change.newDivision}` : change.newRank;
    
    return `${winLoss} <@${change.id}>: ${oldRankDisplay} ${change.oldLP}LP → ${newRankDisplay} ${change.newLP}LP (${changeSymbol} ${changeText} ELO)`;
  }).join('\n');

  // ADD MATCH ID TO THE EMBED TITLE AND DESCRIPTION
  const embed = new EmbedBuilder()
    .setTitle(`📜 Match History - ID: ${matchId}`) // ADD MATCH ID TO TITLE
    .setDescription(`**Match ID:** ${matchId}\n**Winner:** ${winner === "1" ? "🟦 Team 1 (Blue)" : "🟥 Team 2 (Red)"}`) // ADD MATCH ID TO DESCRIPTION
    .addFields(
      { name: "🟦 Team 1 (Blue)", value: team1Players, inline: false },
      { name: "🟥 Team 2 (Red)", value: team2Players, inline: false },
      { name: "📈 ELO Changes", value: eloChangesText || "No changes", inline: false }
    )
    .setColor(winner === "1" ? 0x3498db : 0xe74c3c)
    .setTimestamp()
    .setFooter({ text: `Match ID: ${matchId} | Use !changewinner or !voidmatch with this ID` }); // ADD MATCH ID TO FOOTER

  // Send main history embed
  await historyChannel.send({ embeds: [embed] });

  // Send rank promotions/demotions to both #history AND #general if any occurred
  if (rankChanges.length > 0) {
    const rankChangeText = rankChanges.map(change => {
      const oldDisplay = change.oldDivision ? `${change.oldRank} ${change.oldDivision}` : change.oldRank;
      const newDisplay = change.newDivision ? `${change.newRank} ${change.newDivision}` : change.newRank;
      const emoji = change.isPromotion ? "🎉" : "📉";
      const action = change.isPromotion ? "PROMOTED" : "DEMOTED";
      
      return `${emoji} <@${change.id}> ${action}: **${oldDisplay}** → **${newDisplay}**`;
    }).join('\n');

    const rankChangeEmbed = new EmbedBuilder()
      .setTitle(rankChanges.some(rc => rc.isPromotion) ? `🏆 Rank Promotions - Match ${matchId}` : `📉 Rank Changes - Match ${matchId}`)
      .setDescription(rankChangeText)
      .setColor(rankChanges.some(rc => rc.isPromotion) ? 0x00ff00 : 0xff9900)
      .setTimestamp()
      .setFooter({ text: `Match ID: ${matchId}` });

    // Send to history channel
    await historyChannel.send({ embeds: [rankChangeEmbed] });
  }

  // Fun shoutout if Romeo wins
  if (winners.includes("272603932268822529") && generalChannel) {
    await generalChannel.send("Wow Romeo actually won? That guy is ass");
  }

  // ✅ Send confirmation message BEFORE deleting channels - NOW INCLUDES MATCH ID
  await channel.send(`✅ Match ${matchId} ended! ${winner === "1" ? "🟦 Team 1 (Blue)" : "🟥 Team 2 (Red)"} wins!`);

  // Delete match channels with proper error handling
  try {
    // Delete voice channels first
    if (team1VC) await team1VC.delete().catch(console.error);
    if (team2VC) await team2VC.delete().catch(console.error);
    
    // Delete the match text channel
    if (matchChannel) await matchChannel.delete().catch(console.error);
    
    // Delete the category LAST (after all children are deleted)
    if (matchCategory) await matchCategory.delete().catch(console.error);
    
  } catch (err) {
    console.error("Error deleting match channels:", err);
  }

  // Remove this match from active matches
  matches.delete(channel.id);
  
  // Update leaderboard after match ends
  await updateLeaderboardChannel(guild);
}

// ---------------- READY ----------------
const MAIN_GUILD_ID = "1423242905602101310";

client.once("ready", async () => {
  console.log(`✅ Logged in as ${client.user.tag}`);
  
  // Connect to MongoDB first
  await connectDB();
  
  // Load data from MongoDB/file
  playerData = await loadData();
  
  const guild = client.guilds.cache.get(MAIN_GUILD_ID);
  if (!guild) {
    console.log("Bot is not in the main server!");
    return;
  }

  // Find or create how-to-play channel
  let howtoplayChannel = guild.channels.cache.find(c => c.name === "how-to-play" && c.type === 0);
  if (!howtoplayChannel) {
    howtoplayChannel = await guild.channels.create({ name: "how-to-play", type: 0 });
  }

  // ✅ Post role selection in the channel instead of DMs
  await postRoleSelectionMessage(howtoplayChannel);

  // Queue setup (keep existing)
  let queueChannel = guild.channels.cache.find((c) => c.name === "queue");
  if (!queueChannel) {
    queueChannel = await guild.channels.create({ name: "queue", type: 0 });
  }
  await postQueueMessage(queueChannel);
  
  console.log('✅ Bot fully initialized with data loaded');
});

// ---------------- WEB SERVER FOR RENDER ----------------
const express = require('express');
const app = express();
const port = process.env.PORT || 10000; // Use 10000 to match your logs

// Add request logging to debug health checks
app.use((req, res, next) => {
  console.log(`🌐 ${req.method} ${req.path} - ${new Date().toISOString()}`);
  next();
});

// Enhanced health check with better error handling
app.get('/health', (req, res) => {
  try {
    const healthData = {
      status: 'OK',
      message: 'Discord bot is running',
      timestamp: new Date().toISOString(),
      guilds: client.guilds?.cache?.size || 0,
      uptime: process.uptime(),
      queueSize: queue?.length || 0,
      activeMatches: matches?.size || 0,
      readyCheckActive: !!activeReadyCheck
    };
    
    console.log(`🏥 Health check called - ${healthData.guilds} guilds, ${healthData.queueSize} in queue`);
    
    res.status(200).json(healthData);
  } catch (error) {
    console.error('❌ Health check error:', error);
    res.status(500).json({ 
      status: 'ERROR', 
      error: error.message,
      timestamp: new Date().toISOString()
    });
  }
});

// Root endpoint with redirect to health
app.get('/', (req, res) => {
  res.redirect('/health');
});

// Start the web server with better error handling
const server = app.listen(port, '0.0.0.0', () => {
  console.log(`🟢 Web server running on port ${port}`);
  console.log(`🔗 Health check available at: http://0.0.0.0:${port}/health`);
  console.log(`🌐 Public URL: https://${process.env.RENDER_SERVICE_NAME}.onrender.com/health`);
});

// Handle server errors
server.on('error', (error) => {
  console.error('❌ Server error:', error);
  if (error.code === 'EADDRINUSE') {
    console.log(`⚠️ Port ${port} is already in use. Trying alternative...`);
  }
});

client.login(process.env.BOT_TOKEN);