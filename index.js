// index.js
require("dotenv").config();
const fs = require("fs");
const axios = require("axios");
const cheerio = require("cheerio");
const puppeteer = require('puppeteer-core');
const chromium = require('@sparticuz/chromium');
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
  UserSelectMenuBuilder,
  PermissionsBitField
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
const QUEUE4FUN_SIZE = 10;
const FUN_POINTS_PER_GAME = 50;
const DUO_REQUEST_EXPIRY = 5 * 60 * 1000; // Duo request expiration time (10 minutes)

let queue = [];
let queue4fun = [];
let queueMessage;
let queueMessage4fun;
let leaderboardMessage;
let leaderboardMessage4fun;
let matches = new Map();
let matches4fun = new Map();
let activeReadyCheck = null;
let active4funReadyCheck = null;
let queueEnabled = true;
let bannedUsers = new Set();
let requestCount = 0;
let saveDataTimeout = null;
let pendingDuoRequests = new Map(); // key: requesterId, value: { targetId, timestamp }
let voteMessageTimers = new Map(); // key: channelId, value: timer
let voteMessageFloodCheck = new Map(); // key: channelId, value: { lastMessageCount: number, lastCheck: number }

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
      roles: [],
      currentStreak: 0,
      streakType: "none",
      // 4fun stats
      fun: {
        points: 0,
        wins: 0,
        losses: 0,
        matchesPlayed: 0,
        hiddenMMR: 0 // Will be set based on main rank when they first play
      }
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
  if (player.currentStreak === undefined) player.currentStreak = 0;
  if (player.streakType === undefined) player.streakType = "none";
  
  // Ensure 4fun stats exist
  if (!player.fun) {
    player.fun = {
      points: 0,
      wins: 0,
      losses: 0,
      matchesPlayed: 0,
      hiddenMMR: 0
    };
  }
  
  return playerData[id];
}

// ---------------- MATCH ID GENERATION ----------------
let matchIdCounter = 0;
let matchIdInitialized = false;
let matchIdLock = false;

async function getNextMatchId() {
  // Wait for lock if another match is being created
  while (matchIdLock) {
    await new Promise(resolve => setTimeout(resolve, 100));
  }
  
  try {
    matchIdLock = true;
    
    // If we haven't initialized the counter yet, load from match history
    if (!matchIdInitialized) {
      const matchHistory = await loadMatchHistory();
      
      // If no matches exist, start from 1
      if (matchHistory.length === 0) {
        matchIdCounter = 1;
      } else {
        // Find the highest existing match ID
        const maxId = Math.max(...matchHistory.map(match => {
          // Handle both string and number IDs
          const id = match.id;
          if (typeof id === 'string') {
            const num = parseInt(id);
            return isNaN(num) ? 0 : num;
          } else if (typeof id === 'number') {
            return id;
          }
          return 0;
        }).filter(id => !isNaN(id) && id > 0));
        
        matchIdCounter = maxId + 1;
      }
      matchIdInitialized = true;
      console.log(`🔢 Match ID counter initialized: ${matchIdCounter}`);
    } else {
      // Just increment the counter
      matchIdCounter++;
    }
    
    console.log(`🎯 Generated new match ID: ${matchIdCounter}`);
    return matchIdCounter.toString();
    
  } finally {
    // Always release the lock
    matchIdLock = false;
  }
}

// load/save match history
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
        try {
            const data = fs.readFileSync(MATCH_HISTORY_FILE, 'utf8');
            const history = JSON.parse(data);
            console.log(`📥 Loaded ${history.length} matches from local file`);
            return history;
        } catch (error) {
            console.error('Error loading match history from file:', error);
            return [];
        }
    }
    console.log('📥 No existing match history found');
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

// reset match ID counter on bot restart
async function initializeMatchIdCounter() {
  const matchHistory = await loadMatchHistory();
  
  if (matchHistory.length === 0) {
    matchIdCounter = 1;
  } else {
    // Find the highest existing match ID
    const maxId = Math.max(...matchHistory.map(match => {
      const id = match.id;
      if (typeof id === 'string') {
        const num = parseInt(id);
        return isNaN(num) ? 0 : num;
      } else if (typeof id === 'number') {
        return id;
      }
      return 0;
    }).filter(id => !isNaN(id) && id > 0));
    
    matchIdCounter = maxId + 1;
  }
  matchIdInitialized = true;
  console.log(`🔢 Match ID counter initialized: ${matchIdCounter}`);
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
                
                // ✅ ADD THIS: Convert smurf refund Sets
                if (data._smurfRefunds) {
                    if (data._smurfRefunds.processedMatches) {
                        data._smurfRefunds.processedMatches = new Set(data._smurfRefunds.processedMatches);
                    }
                    if (data._smurfRefunds.processedSmurfs) {
                        data._smurfRefunds.processedSmurfs = new Set(data._smurfRefunds.processedSmurfs);
                    }
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
        
        // ✅ ADD THIS: Convert smurf refund Sets for file loading too
        if (data._smurfRefunds) {
            if (data._smurfRefunds.processedMatches) {
                data._smurfRefunds.processedMatches = new Set(data._smurfRefunds.processedMatches);
            }
            if (data._smurfRefunds.processedSmurfs) {
                data._smurfRefunds.processedSmurfs = new Set(data._smurfRefunds.processedSmurfs);
            }
        }
        
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

// ---------------- HELPER FUNCTIONS ----------------
// Manages the vote status message
async function updateOrCreateVoteMessage(channel, match, is4fun = false) {
  const team1Votes = match.votes.team1.size;
  const team2Votes = match.votes.team2.size;
  const totalVotes = team1Votes + team2Votes;
  
  const voteMessageContent = `🗳️ **${is4fun ? '4Fun Match' : 'Match'} Voting**\n\n` +
    `**Current Vote Count:**\n` +
    `🔵 Team 1: ${team1Votes} votes\n` +
    `🔴 Team 2: ${team2Votes} votes\n` +
    `📊 Total: ${totalVotes}/10 players\n\n` +
    `*6 votes for one team ends the match*`;

  const voteButtonsRow = new ActionRowBuilder().addComponents(
    new ButtonBuilder()
      .setCustomId(`report_${is4fun ? '4fun_' : ''}win_1`)
      .setLabel('🏆 Team 1 Won')
      .setStyle(ButtonStyle.Success),
    new ButtonBuilder()
      .setCustomId(`report_${is4fun ? '4fun_' : ''}win_2`)
      .setLabel('🏆 Team 2 Won')
      .setStyle(ButtonStyle.Success)
  );

  // Try to update existing vote message first
  if (match.voteMessageId) {
    try {
      const existingMessage = await channel.messages.fetch(match.voteMessageId);
      await existingMessage.edit({
        content: voteMessageContent,
        components: [voteButtonsRow]
      });
      console.log(`✅ Updated existing vote message ${match.voteMessageId}`);
      return; // Successfully updated
    } catch (error) {
      // Message was deleted or not found
      console.log('❌ Vote message not found, creating new one');
      match.voteMessageId = null;
    }
  }

  // ALWAYS create a new vote message when flood is detected or initial timer expires
  console.log(`🆕 Creating new vote message in channel ${channel.id}`);
  const newVoteMessage = await channel.send({
    content: voteMessageContent,
    components: [voteButtonsRow]
  });
  match.voteMessageId = newVoteMessage.id;
  console.log(`✅ Created new vote message with ID: ${newVoteMessage.id}`);
}

// Add this new function to handle the initial 20-minute delay and flood monitoring
async function startVoteMessageFloodMonitoring(channel, match, is4fun = false) {
  const channelId = channel.id;
  
  // Clear any existing timer for this channel
  if (voteMessageTimers.has(channelId)) {
    clearTimeout(voteMessageTimers.get(channelId));
  }
  
  console.log(`⏰ Starting 20-minute timer for vote message in channel ${channelId}`);
  
  // Set initial 20-minute timer
  const initialTimer = setTimeout(async () => {
    console.log(`⏰ 20 minutes passed, sending initial vote message for channel ${channelId}`);
    
    // Check if match still exists
    const matchMap = is4fun ? matches4fun : matches;
    if (!matchMap.has(channelId)) {
      console.log(`❌ Match ended before 20-minute timer, cancelling vote message`);
      return;
    }
    
    await updateOrCreateVoteMessage(channel, match, is4fun);
    
    // Start periodic flood checks after initial message
    startPeriodicFloodCheck(channel, match, is4fun);
  }, 20 * 60 * 1000); // 20 minutes
  
  voteMessageTimers.set(channelId, initialTimer);
}

// Periodically check for flood conditions
async function startPeriodicFloodCheck(channel, match, is4fun = false) {
  const channelId = channel.id;
  
  const checkFlood = async () => {
    // Check if match still exists
    const matchMap = is4fun ? matches4fun : matches;
    if (!matchMap.has(channelId)) {
      console.log(`❌ Match no longer exists in channel ${channelId}, stopping flood check`);
      return;
    }
    
    if (!match.voteMessageId) {
      console.log(`⚠️ No vote message ID for channel ${channelId}, creating one`);
      await updateOrCreateVoteMessage(channel, match, is4fun);
    } else {
      try {
        // Fetch recent messages to check if vote buttons are visible
        const messages = await channel.messages.fetch({ limit: 50 });
        const messageArray = Array.from(messages.values());
        
        // Find the vote message in the recent messages
        const voteMessageIndex = messageArray.findIndex(msg => msg.id === match.voteMessageId);
        
        // If vote message is not in the last 20 messages, it's considered "flooded"
        const floodThreshold = 20;
        const isFlooded = voteMessageIndex === -1 || voteMessageIndex >= floodThreshold;
        
        if (isFlooded) {
          console.log(`🌊 Chat flooded in channel ${channelId}, vote message index: ${voteMessageIndex}, resending vote message`);
          // Force create a new message by nullifying the old ID
          match.voteMessageId = null;
          await updateOrCreateVoteMessage(channel, match, is4fun);
        } else {
          console.log(`✅ Vote message visible at index ${voteMessageIndex} in channel ${channelId}`);
        }
      } catch (error) {
        console.error('❌ Error checking flood condition:', error);
      }
    }
    
    // Continue monitoring unless match has ended
    if (matchMap.has(channelId)) {
      setTimeout(checkFlood, 30 * 1000); // Check every 30 seconds
    }
  };
  
  // Start the first check after 30 seconds
  setTimeout(checkFlood, 30 * 1000);
}

// Add this function to clean up timers when match ends
function cleanupVoteTimers(channelId) {
  if (voteMessageTimers.has(channelId)) {
    clearTimeout(voteMessageTimers.get(channelId));
    voteMessageTimers.delete(channelId);
  }
  if (voteMessageFloodCheck.has(channelId)) {
    voteMessageFloodCheck.delete(channelId);
  }
}

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

  // Calculate average rank of all players who have played games
  let totalIHP = 0;
  let playerCount = 0;
  
  Object.keys(playerData).forEach(id => {
    if (id.startsWith('_')) return false;
    
    const p = playerData[id];
    const hasPlayedGames = (p.wins + p.losses) > 0;
    
    if (p && typeof p === 'object' && p.rank !== undefined && hasPlayedGames) {
      totalIHP += getIHP(p);
      playerCount++;
    }
  });

  // Calculate average rank - ROUND IHP to avoid decimal LP
  const averageIHP = playerCount > 0 ? Math.round(totalIHP / playerCount) : 0;
  const averageRank = IHPToRank(averageIHP);
  const averageRankDisplay = formatRankDisplay(averageRank.rank, averageRank.division, averageRank.lp);

  // Build leaderboard sorted by Elo/IHP - FILTER OUT SYSTEM KEYS AND PLAYERS WITH NO GAMES
  const players = Object.keys(playerData)
    .filter(id => {
      // Exclude system keys that start with underscore
      if (id.startsWith('_')) return false;
      
      // Ensure it's a valid player object with required properties
      const p = playerData[id];
      const hasPlayedGames = (p.wins + p.losses) > 0;
      
      return p && typeof p === 'object' && p.rank !== undefined && hasPlayedGames;
    })
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
  
  // If no players, show empty leaderboard
  if (players.length === 0) {
    const embed = new EmbedBuilder()
      .setTitle("🏆 Leaderboard")
      .setDescription("No players have completed any games yet. Play your first match to appear on the leaderboard!")
      .setColor(0xffd700)
      .setTimestamp();
    embeds.push(embed);
  } else {
    for (let i = 0; i < players.length; i += chunkSize) {
      const chunk = players.slice(i, i + chunkSize);
      const description = chunk
        .map((p, idx) => {
          const rankDiv = p.division ? `${p.rank} ${p.division}` : p.rank;
          const line1 = `#${i + idx + 1} • ${rankDiv} ${p.lp} LP`;
          const line2 = `<@${p.id}> | Elo: ${p.elo} | W: ${p.wins} | L: ${p.losses} | WR: ${p.wr}% | GP: ${p.gp}`;
          return `${line1}\n${line2}`;
        })
        .join("\n\n");

      const embed = new EmbedBuilder()
        .setTitle(i === 0 ? "🏆 Leaderboard" : `Leaderboard (cont.)`)
        .setDescription(
          i === 0 
            ? `**Average Rank in All Matches Played: ${averageRankDisplay}**\n\n${description}`
            : description
        )
        .setColor(0xffd700)
        .setTimestamp();
      embeds.push(embed);
    }
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

async function update4funLeaderboardChannel(guild) {
  const channelName = "4fun-leaderboard";
  let lbChannel = guild.channels.cache.find(c => c.name === channelName && c.type === 0);
  if (!lbChannel) {
    lbChannel = await guild.channels.create({ name: channelName, type: 0 });
  }

  if (!leaderboardMessage4fun || !leaderboardMessage4fun.length) {
    const fetched = await lbChannel.messages.fetch({ limit: 20 });
    const existing = fetched.filter(m => m.author.id === client.user.id && m.embeds.length > 0);
    if (existing.size > 0) {
      leaderboardMessage4fun = Array.from(existing.values()).sort((a, b) => a.createdTimestamp - b.createdTimestamp);
      console.log(`Found ${leaderboardMessage4fun.length} existing 4fun leaderboard messages.`);
    } else {
      leaderboardMessage4fun = [];
    }
  }

  // Build 4fun leaderboard - only include players that have played 4fun matches
  const players = Object.keys(playerData)
    .filter(id => {
      if (id.startsWith('_')) return false;
      const p = playerData[id];
      const hasPlayed4fun = p.fun?.matchesPlayed > 0;
      return p && typeof p === 'object' && p.fun && hasPlayed4fun;
    })
    .map(id => {
      const p = playerData[id];
      const fun = p.fun;
      const normalRankDisplay = formatRankDisplay(p.rank, p.division, p.lp);
      const wr = fun.matchesPlayed > 0 ? ((fun.wins / fun.matchesPlayed) * 100).toFixed(1) : "0.0";
      return {
        id,
        normalRankDisplay,
        points: fun.points,
        wins: fun.wins,
        losses: fun.losses,
        wr,
        matchesPlayed: fun.matchesPlayed
      };
    })
    .sort((a, b) => b.points - a.points); // highest 4fun points first

  const chunkSize = 25;
  const embeds = [];
  
  if (players.length === 0) {
    const embed = new EmbedBuilder()
      .setTitle("🏆 4Fun Leaderboard")
      .setDescription("No players have completed any 4fun matches yet. Play your first 4fun match to appear on the leaderboard!")
      .setColor(0xff00ff)
      .setTimestamp();
    embeds.push(embed);
  } else {
    for (let i = 0; i < players.length; i += chunkSize) {
      const chunk = players.slice(i, i + chunkSize);
      const description = chunk
        .map((p, idx) => {
          const line1 = `#${i + idx + 1} • ${p.normalRankDisplay} • ${p.points} 4fun pts`;
          const line2 = `<@${p.id}> | W: ${p.wins} | L: ${p.losses} | WR: ${p.wr}% | GP: ${p.matchesPlayed}`;
          return `${line1}\n${line2}`;
        })
        .join("\n\n");

      const embed = new EmbedBuilder()
        .setTitle(i === 0 ? "🏆 4Fun Leaderboard" : `4Fun Leaderboard (cont.)`)
        .setDescription(description)
        .setColor(0xff00ff)
        .setTimestamp();
      embeds.push(embed);
    }
  }

  if (leaderboardMessage4fun && leaderboardMessage4fun.length) {
    for (let i = 0; i < embeds.length; i++) {
      const embed = embeds[i];
      if (leaderboardMessage4fun[i]) {
        await leaderboardMessage4fun[i].edit({ embeds: [embed] }).catch(() => {});
      } else {
        const msg = await lbChannel.send({ embeds: [embed] });
        leaderboardMessage4fun.push(msg);
      }
    }
    if (leaderboardMessage4fun.length > embeds.length) {
      for (let i = embeds.length; i < leaderboardMessage4fun.length; i++) {
        await leaderboardMessage4fun[i].delete().catch(() => {});
      }
      leaderboardMessage4fun = leaderboardMessage4fun.slice(0, embeds.length);
    }
  } else {
    leaderboardMessage4fun = [];
    for (const embed of embeds) {
      const msg = await lbChannel.send({ embeds: [embed] });
      leaderboardMessage4fun.push(msg);
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

async function start4funReadyCheck(channel) {
  if (queue4fun.length !== QUEUE4FUN_SIZE) {
    console.warn(`⚠️ 4fun Ready check attempted with ${queue4fun.length} players, expected ${QUEUE4FUN_SIZE}`);
    return;
  }
  
  if (active4funReadyCheck) {
    console.warn("⚠️ 4fun Ready check already active, ignoring duplicate");
    return;
  }

  const participants = [...queue4fun];
  const ready = new Set();
  const declined = new Set();
  const TIMEOUT = 60;
  const endTime = Date.now() + (TIMEOUT * 1000);

  let pendingUpdate = false;
  let updateTimeout = null;
  const DEBOUNCE_DELAY = 300;

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
        console.log('Edit error during 4fun ready check:', error.message);
        pendingUpdate = false;
      }
    }, DEBOUNCE_DELAY);
  };

  const row = new ActionRowBuilder().addComponents(
    new ButtonBuilder()
      .setCustomId("ready4fun")
      .setLabel("✅ Ready")
      .setStyle(ButtonStyle.Success),
    new ButtonBuilder()
      .setCustomId("notready4fun")
      .setLabel("❌ Decline")
      .setStyle(ButtonStyle.Danger)
  );

  const msg = await channel.send({
    content: participants.map((id) => `<@${id}>`).join(" "),
    embeds: [createReadyCheckEmbed()],
    components: [row],
  });

  const collector = msg.createMessageComponentCollector({ time: TIMEOUT * 1000 });
  active4funReadyCheck = { msg, collector };

  collector.on("collect", async (i) => {
    if (!participants.includes(i.user.id)) {
        return i.reply({ content: "You're not in this 4fun queue.", ephemeral: true });
    }

    if (i.customId === "notready4fun") {
        console.log("4fun Decline button clicked by:", i.user.id);
        
        queue4fun = queue4fun.filter((id) => id !== i.user.id);
        declined.add(i.user.id);
        saveData();
        await update4funQueueMessage();

        await i.reply({
            content: `❌ You have declined the 4fun queue.`,
            ephemeral: true,
        });
        
        await msg.channel.send({
            content: `⚠️ <@${i.user.id}> declined the 4fun ready check.`
        });
        
        collector.stop("declined");
        return;
    }

    if (ready.has(i.user.id)) {
        await i.deferUpdate().catch(() => {});
        return;
    }

    ready.add(i.user.id);
    debouncedUpdate();

    await i.deferUpdate().catch((err) => {
      if (err.code !== 10062) console.error("4fun Button deferUpdate error:", err);
    });

    if (ready.size === participants.length) {
      if (updateTimeout) {
        clearTimeout(updateTimeout);
      }
      try {
        const updatedEmbed = createReadyCheckEmbed();
        await msg.edit({ embeds: [updatedEmbed] }).catch(() => {});
      } catch (error) {
        console.log('Edit error during 4fun ready check:', error.message);
      }
      collector.stop("all_ready");
    }
    return;
  });
  
  collector.on("end", async (_, reason) => {
    if (updateTimeout) {
      clearTimeout(updateTimeout);
    }
    active4funReadyCheck = null;

    let description = "";
    if (reason === "all_ready") {
        description = "✅ All players ready. 4Fun Match is starting!";
    } else if (reason === "declined") {
        description = "❌ A player declined the 4fun ready check. Match canceled.";
    } else {
        description = "⌛ 4fun Ready check timed out. Match canceled.";
        
        const notReady = participants.filter((id) => !ready.has(id) && !declined.has(id));
        if (notReady.length > 0) {
            queue4fun = queue4fun.filter((id) => !notReady.includes(id));
            saveData();
            await update4funQueueMessage();
            
            await msg.channel.send({
                content: `⌛ 4fun Ready check timed out. The following players did not respond: ${notReady.map(id => `<@${id}>`).join(", ")}`
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

    setTimeout(async () => {
      try {
        const freshMessage = await msg.channel.messages.fetch(msg.id).catch(() => null);
        if (freshMessage && freshMessage.deletable) {
          await freshMessage.delete();
          console.log('✅ 4fun Ready check embed deleted after completion');
        }
      } catch (error) {
        if (error.code !== 10008) {
          console.error('Error deleting 4fun ready check embed:', error);
        }
      }
    }, 50000);

    if (reason === "all_ready") {
        await make4funTeams(channel);
    } else {
        await update4funQueueMessage();
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
  let browser = null;
  try {
    console.log('🔄 Launching Puppeteer browser for draftlol.dawe.gg...');

    // Launch the browser using the bundled Chromium
    browser = await puppeteer.launch({
      args: chromium.args,
      defaultViewport: chromium.defaultViewport,
      executablePath: await chromium.executablePath(),
      headless: chromium.headless,
      ignoreHTTPSErrors: true,
    });

    console.log('✅ Browser launched, creating new page...');
    const page = await browser.newPage();
    
    // Set a reasonable timeout
    await page.setDefaultTimeout(60000);
    
    // Set viewport to ensure elements are visible
    await page.setViewport({ width: 1280, height: 720 });
    
    // Navigate to draftlol homepage
    console.log('🌐 Navigating to draftlol.dawe.gg...');
    await page.goto('https://draftlol.dawe.gg/', { 
      waitUntil: 'networkidle2',
      timeout: 60000
    });

    // Wait for the page to load completely
    console.log('⏳ Waiting for page to load...');
    await page.waitForSelector('body', { timeout: 15000 });
    
    // Wait for the create lobby button to be available and clickable
    console.log('🔍 Looking for Create Lobby button...');
    await page.waitForSelector('div.sendButton', { timeout: 20000 });
    
    // Click "Create Lobby"
    console.log('🖱️ Clicking Create Lobby button...');
    await page.click('div.sendButton');
    
    // Wait for the lobby creation to complete and links to appear
    console.log('⏳ Waiting for lobby creation and links to generate...');
    
    // Wait for the input fields to appear and have values
    await page.waitForFunction(() => {
      const blueInput = document.querySelector('.inputBlue');
      const redInput = document.querySelector('.inputRed');
      const inputs = Array.from(document.querySelectorAll('input[type=text]'));
      const spectatorInput = inputs.find(input => 
        !input.classList.contains('inputBlue') && 
        !input.classList.contains('inputRed')
      );
      
      return blueInput && blueInput.value && 
             redInput && redInput.value && 
             spectatorInput && spectatorInput.value &&
             blueInput.value.includes('draftlol.dawe.gg/') &&
             redInput.value.includes('draftlol.dawe.gg/') &&
             spectatorInput.value.includes('draftlol.dawe.gg/');
    }, { timeout: 30000, polling: 1000 });
    
    console.log('✅ Lobby created successfully, extracting links...');
    
    // Grab all three links from the input fields
    const links = await page.evaluate(() => {
      const blueInput = document.querySelector('.inputBlue');
      const redInput = document.querySelector('.inputRed');
      
      // Find the spectator input (third input that's not blue or red)
      const inputs = Array.from(document.querySelectorAll('input[type=text]'));
      const spectatorInput = inputs.find(input => 
        !input.classList.contains('inputBlue') && 
        !input.classList.contains('inputRed')
      );
      
      const blue = blueInput?.value?.trim() || '';
      const red = redInput?.value?.trim() || '';
      const spectator = spectatorInput?.value?.trim() || '';
      
      console.log('Extracted links:', { blue, red, spectator });
      return { blue, red, spectator };
    });

    // Validate that we got proper draft links
    if (!links.blue || !links.red || !links.spectator || 
        !links.blue.includes('draftlol.dawe.gg/') || 
        !links.red.includes('draftlol.dawe.gg/') || 
        !links.spectator.includes('draftlol.dawe.gg/')) {
      
      console.error('❌ Invalid links extracted:', links);
      throw new Error('Failed to extract valid draft links');
    }

    console.log('✅ Draft lobby created successfully!');
    console.log(`🔵 Blue: ${links.blue}`);
    console.log(`🔴 Red: ${links.red}`);
    console.log(`👁️ Spectator: ${links.spectator}`);
    
    return {
      blue: links.blue,
      red: links.red,
      spectator: links.spectator
    };

  } catch (error) {
    console.error('❌ Puppeteer error creating draft lobby:', error);
    
    // Provide more detailed error information
    if (error.message.includes('timeout')) {
      throw new Error('Draft lobby creation timed out. Please try again or create draft links manually at https://draftlol.dawe.gg');
    } else if (error.message.includes('Failed to extract valid draft links')) {
      throw new Error('Draft links were not generated properly. Please create draft links manually at https://draftlol.dawe.gg');
    } else {
      throw new Error('Failed to create draft lobby automatically. Please create draft links manually at https://draftlol.dawe.gg');
    }
  } finally {
    // Always close the browser
    if (browser) {
      await browser.close().catch(console.error);
      console.log('🔒 Browser closed');
    }
  }
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

function build4funQueueEmbed() {
  // Group duos in queue
  const duosInQueue = [];
  const soloInQueue = [];
  const processed = new Set();

  queue4fun.forEach(playerId => {
    if (processed.has(playerId)) return;

    const player = ensurePlayer(playerId);
    if (player.fun.duoPartner && queue4fun.includes(player.fun.duoPartner)) {
      duosInQueue.push([playerId, player.fun.duoPartner]);
      processed.add(playerId);
      processed.add(player.fun.duoPartner);
    } else {
      soloInQueue.push(playerId);
      processed.add(playerId);
    }
  });

  let queueDescription = "";

  // Display duos
  if (duosInQueue.length > 0) {
    queueDescription += "**🤝 Duos:**\n";
    duosInQueue.forEach((duo, index) => {
      queueDescription += `${index + 1}. <@${duo[0]}> + <@${duo[1]}>\n`;
    });
    queueDescription += "\n";
  }

  // Display solo players
  if (soloInQueue.length > 0) {
    queueDescription += "**👤 Solo Players:**\n";
    soloInQueue.forEach((playerId, index) => {
      queueDescription += `${duosInQueue.length + index + 1}. <@${playerId}>\n`;
    });
  }

  if (queue4fun.length === 0) {
    queueDescription = "The 4fun queue is currently empty.";
  }

  const embed = new EmbedBuilder()
    .setTitle("🎉 4Fun Queue - Howling Abyss 5v5 Blind Pick")
    .setColor(0x00ff00)
    .setDescription(queueDescription + `\nStatus: **OPEN**`)
    .setFooter({ 
      text: `Queue: ${queue4fun.length}/${QUEUE4FUN_SIZE} | Duos: ${duosInQueue.length}` 
    })
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

async function post4funQueueMessage(channel) {
  // Check for an existing queue message with better filtering
  const existing = (await channel.messages.fetch({ limit: 50 })) // Increase limit to 50
    .filter(m => 
      m.author.id === client.user.id && 
      m.embeds.length > 0 && 
      m.embeds[0].title && 
      m.embeds[0].title.includes("4Fun Queue") // More flexible matching
    )
    .first();

  if (existing) {
    console.log("4Fun Queue message already exists — reusing it.");
    queueMessage4fun = existing;
    await update4funQueueMessage();
    return existing; // Return the existing message
  }

  // Create new message if none exists
  const row = new ActionRowBuilder().addComponents(
    new ButtonBuilder().setCustomId("join4fun").setLabel("✅ Join Queue").setStyle(ButtonStyle.Success),
    new ButtonBuilder().setCustomId("leave4fun").setLabel("🚪 Leave Queue").setStyle(ButtonStyle.Danger),
    new ButtonBuilder().setCustomId("duo4fun").setLabel("🤝 Request Duo").setStyle(ButtonStyle.Primary)
  );

  const embed = build4funQueueEmbed();
  queueMessage4fun = await channel.send({ embeds: [embed], components: [row] });
  return queueMessage4fun;
}

let update4funQueueTimeout = null;
async function update4funQueueMessage() {
  trackRequest();
  if (!queueMessage4fun) return;

  if (update4funQueueTimeout) {
    clearTimeout(update4funQueueTimeout);
  }

  update4funQueueTimeout = setTimeout(async () => {
    const row = new ActionRowBuilder().addComponents(
      new ButtonBuilder().setCustomId("join4fun").setLabel("✅ Join Queue").setStyle(ButtonStyle.Success),
      new ButtonBuilder().setCustomId("leave4fun").setLabel("🚪 Leave Queue").setStyle(ButtonStyle.Danger),
      new ButtonBuilder().setCustomId("duo4fun").setLabel("🤝 Request Duo").setStyle(ButtonStyle.Primary) // ADD THIS
    );

    const embed = build4funQueueEmbed();
    await queueMessage4fun.edit({ embeds: [embed], components: [row] });
  }, 250);
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
  if (interaction.isUserSelectMenu() && interaction.customId === 'duo_partner_select') {
    const selectedUserId = interaction.values[0]; // The selected user's ID
    const requesterId = interaction.user.id;

    // Use the same validation logic you had in your modal
    if (selectedUserId === requesterId) {
        return interaction.reply({
            content: "❌ You cannot request a duo with yourself.",
            ephemeral: true
        });
    }

    const requester = ensurePlayer(requesterId);
    const target = ensurePlayer(selectedUserId);

    // Validate target player
    if (!target.summonerName) {
        return interaction.reply({
            content: "❌ That player is not registered. They need to use `!register` first.",
            ephemeral: true
        });
    }

    if (target.fun.duoPartner) {
        return interaction.reply({
            content: `❌ <@${selectedUserId}> is already in a duo with <@${target.fun.duoPartner}>.`,
            ephemeral: true
        });
    }

    // Check if target is in queue
    const targetInQueue = queue4fun.includes(selectedUserId);

    // Find the duo-requests channel
    const duoRequestsChannel = interaction.guild.channels.cache.find(
        channel => channel.name === 'duo-requests' && channel.type === 0
    );

    if (!duoRequestsChannel) {
        return interaction.update({
            content: '❌ Error: #duo-requests channel not found. Please contact an admin.',
            components: []
        });
    }

    try {
        // Calculate expiration timestamp (5 minutes from now)
        const expirationTimestamp = Math.floor((Date.now() + DUO_REQUEST_EXPIRY) / 1000);
        
        // Create the embed for the duo request with Discord timestamp
        const embed = new EmbedBuilder()
            .setTitle("🤝 Duo Request")
            .setDescription(`<@${requesterId}> wants to form a duo with <@${selectedUserId}> for 4fun queue!`)
            .addFields(
                { name: "Requester", value: `<@${requesterId}>`, inline: true },
                { name: "Target", value: `<@${selectedUserId}>`, inline: true },
                { name: "Queue Status", value: targetInQueue ? "✅ Target in queue" : "❌ Target not in queue", inline: true },
                { name: "Expires", value: `<t:${expirationTimestamp}:R>`, inline: true }
            )
            .setColor(0x0099FF)
            .setTimestamp();

          const row = new ActionRowBuilder().addComponents(
            new ButtonBuilder()
                .setCustomId(`accept_duo_${requesterId}_${selectedUserId}`)
                .setLabel("✅ Accept")
                .setStyle(ButtonStyle.Success),
            new ButtonBuilder()
                .setCustomId(`decline_duo_${requesterId}_${selectedUserId}`)
                .setLabel("❌ Decline")
                .setStyle(ButtonStyle.Danger)
          );

        // Send the duo request to the #duo-requests channel
        const duoMessage = await duoRequestsChannel.send({ 
            content: `<@${selectedUserId}>`, // Ping the target user
            embeds: [embed], 
            components: [row] 
        });

        // Create the request data object
        const requestData = {
            targetId: selectedUserId,
            timestamp: Date.now(),
            messageId: duoMessage.id,
            channelId: duoRequestsChannel.id,
            expirationTimestamp: expirationTimestamp // Store the timestamp for reference
        };

        // Remove the countdown interval and just keep the expiration timer
        requestData.timer = setTimeout(async () => {
            if (pendingDuoRequests.has(requesterId)) {
                const expiredRequest = pendingDuoRequests.get(requesterId);
                pendingDuoRequests.delete(requesterId);
                
                // Update the message to show it expired
                try {
                    const channel = interaction.guild.channels.cache.get(expiredRequest.channelId);
                    if (channel) {
                        const message = await channel.messages.fetch(expiredRequest.messageId);
                        const expiredEmbed = EmbedBuilder.from(message.embeds[0])
                            .setColor(0xff0000)
                            .spliceFields(3, 1, { name: "Status", value: "❌ Expired", inline: true });
                        
                        await message.edit({ 
                            embeds: [expiredEmbed], 
                            components: [] 
                        });
                    }
                } catch (error) {
                    console.error("Failed to update expired duo request:", error);
                }
                
                console.log(`⏰ Duo request from ${requesterId} expired after 5 minutes`);
            }
        }, DUO_REQUEST_EXPIRY);

        // Store the request data
        pendingDuoRequests.set(requesterId, requestData);

        // Update the original interaction
        await interaction.update({
            content: `✅ Duo request sent to <@${selectedUserId}> in ${duoRequestsChannel}! They have 5 minutes to accept.`,
            components: []
        });

    } catch (error) {
        console.error("Failed to send duo request:", error);
        await interaction.reply({
            content: "❌ Could not send duo request. Please try again.",
            ephemeral: true
        });
    }
  }

  // ---------------- BUTTONS ----------------
  if (interaction.isButton()) {
    const id = interaction.user.id;
    if (interaction.component?.style === ButtonStyle.Link) {
      // Find the match for this channel
      const match = matches.get(interaction.channelId);
      if (!match || !match.drafters) return;
      
      const userId = interaction.user.id;
      
      // Check if user is allowed to use this draft link
      const isBlueDrafter = userId === match.drafters.blue;
      const isRedDrafter = userId === match.drafters.red;
      
      if (interaction.component.url === match.blue && !isBlueDrafter) {
        return interaction.reply({
          content: "❌ Only the assigned blue team drafter can use this link.",
          ephemeral: true
        });
      }
      
      if (interaction.component.url === match.red && !isRedDrafter) {
        return interaction.reply({
          content: "❌ Only the assigned red team drafter can use this link.",
          ephemeral: true
        });
      }
      
      // Allow spectators and drafters to proceed
      return interaction.reply({
        content: "✅ Opening draft link...",
        ephemeral: true
      });
    }

    // --- Draft Link Buttons ---
    if (interaction.customId === 'blue_draft' || interaction.customId === 'red_draft' || interaction.customId === 'spectator_draft') {
      // Find the match for this channel
      const match = matches.get(interaction.channelId);
      if (!match) {
        return interaction.reply({
          content: "❌ No active match found or draft links not available.",
          ephemeral: true
        });
      }

      const userId = interaction.user.id;
      let link = '';
      let message = '';

      if (interaction.customId === 'blue_draft') {
        // Check if user is staff OR the assigned blue drafter
        const isStaff = interaction.member.permissions.has(PermissionsBitField.Flags.ManageMessages);
        const isAssignedDrafter = match.drafters && userId === match.drafters.blue;
        
        if (!isStaff && !isAssignedDrafter) {
          return interaction.reply({
            content: `❌ Only staff members or the assigned blue team drafter (<@${match.drafters?.blue}>) can access this draft link.`,
            ephemeral: true
          });
        }
        link = match.blue;
        message = '🔵 **Blue Team Draft Link**';
      } 
      else if (interaction.customId === 'red_draft') {
        // Check if user is staff OR the assigned red drafter
        const isStaff = interaction.member.permissions.has(PermissionsBitField.Flags.ManageMessages);
        const isAssignedDrafter = match.drafters && userId === match.drafters.red;
        
        if (!isStaff && !isAssignedDrafter) {
          return interaction.reply({
            content: `❌ Only staff members or the assigned red team drafter (<@${match.drafters?.red}>) can access this draft link.`,
            ephemeral: true
          });
        }
        link = match.red;
        message = '🔴 **Red Team Draft Link**';
      }
      else if (interaction.customId === 'spectator_draft') {
        // Spectator link is available to ANYONE in the server
        link = match.spectator;
        message = '👁️ **Spectator Link**';
      }

      // Debug logging to see what links are being retrieved
      console.log(`🔗 Retrieved draft link for ${interaction.customId}:`, link);

      // Check if we have a valid link (not just the base URL)
      if (!link || link === 'https://draftlol.dawe.gg' || !link.includes('draftlol.dawe.gg/')) {
        console.error('❌ Invalid draft link retrieved from match object:', link);
        return interaction.reply({
          content: `❌ Draft link is not available or failed to generate. Please create draft links manually at https://draftlol.dawe.gg`,
          ephemeral: true
        });
      }

      await interaction.reply({
        content: `${message}\n${link}`,
        ephemeral: true
      });
    }

    // Similarly update the 4fun draft link buttons:
    if (interaction.customId === 'blue_draft_4fun' || interaction.customId === 'red_draft_4fun' || interaction.customId === 'spectator_draft_4fun') {
      const match = matches4fun.get(interaction.channelId);
      if (!match) {
        return interaction.reply({
          content: "❌ No active 4fun match found or draft links not available.",
          ephemeral: true
        });
      }

      const userId = interaction.user.id;
      let link = '';
      let message = '';

      if (interaction.customId === 'blue_draft_4fun') {
        // Check if user is staff OR the assigned blue drafter
        const isStaff = interaction.member.permissions.has(PermissionsBitField.Flags.ManageMessages);
        const isAssignedDrafter = match.drafters && userId === match.drafters.blue;
        
        if (!isStaff && !isAssignedDrafter) {
          return interaction.reply({
            content: `❌ Only staff members or the assigned blue team drafter (<@${match.drafters?.blue}>) can access this draft link.`,
            ephemeral: true
          });
        }
        link = match.blue;
        message = '🔵 **Blue Team Draft Link**';
      } 
      else if (interaction.customId === 'red_draft_4fun') {
        // Check if user is staff OR the assigned red drafter
        const isStaff = interaction.member.permissions.has(PermissionsBitField.Flags.ManageMessages);
        const isAssignedDrafter = match.drafters && userId === match.drafters.red;
        
        if (!isStaff && !isAssignedDrafter) {
          return interaction.reply({
            content: `❌ Only staff members or the assigned red team drafter (<@${match.drafters?.red}>) can access this draft link.`,
            ephemeral: true
          });
        }
        link = match.red;
        message = '🔴 **Red Team Draft Link**';
      }
      else if (interaction.customId === 'spectator_draft_4fun') {
        // Spectator link is available to ANYONE in the server
        link = match.spectator;
        message = '👁️ **Spectator Link**';
      }

      // Debug logging
      console.log(`🔗 Retrieved 4fun draft link for ${interaction.customId}:`, link);

      // Check if we have a valid link
      if (!link || link === 'https://draftlol.dawe.gg' || !link.includes('draftlol.dawe.gg/')) {
        console.error('❌ Invalid 4fun draft link retrieved:', link);
        return interaction.reply({
          content: `❌ Draft link is not available or failed to generate. Please create draft links manually at https://draftlol.dawe.gg`,
          ephemeral: true
        });
      }

      await interaction.reply({
        content: `${message}\n${link}`,
        ephemeral: true
      });
    }

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

    if (interaction.customId.startsWith("report_win_")) {
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
      const isStaff = interaction.member.permissions.has(PermissionsBitField.Flags.ManageMessages);
      
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
      const team1Votes = match.votes.team1.size;
      const team2Votes = match.votes.team2.size;
      
      // Update or create vote status message
      await updateOrCreateVoteMessage(interaction.channel, match, false);
      
      // Check for win condition (6 votes for one team)
      if (team1Votes >= 6) {
        await interaction.channel.send(`🏆 **Team 1 has reached 6 votes! Match ending...**`);
        await endMatch(interaction.channel, "1");
      } else if (team2Votes >= 6) {
        await interaction.channel.send(`🏆 **Team 2 has reached 6 votes! Match ending...**`);
        await endMatch(interaction.channel, "2");
      } else {
        // Just acknowledge the vote without showing a reply
        await interaction.deferUpdate().catch(() => {});
      }
    }

    else if (interaction.customId.startsWith("report_4fun_win_")) {
      const team = interaction.customId.split("_")[3];
      
      const match = matches4fun.get(interaction.channelId);
      if (!match) {
        return interaction.reply({ 
          content: "❌ No active 4fun match found in this channel.", 
          ephemeral: true 
        });
      }
      
      const playerId = interaction.user.id;
      const isStaff = interaction.member.permissions.has(PermissionsBitField.Flags.ManageMessages);
      
      if (isStaff) {
        await end4funMatch(interaction.channel, team);
        return interaction.reply({ 
          content: `✅ Staff override: 4fun Match result recorded! Team ${team} wins!`, 
          ephemeral: true 
        });
      }
      
      const isInMatch = match.team1.includes(playerId) || match.team2.includes(playerId);
      if (!isInMatch) {
        return interaction.reply({ 
          content: "❌ You are not a player in this 4fun match and cannot vote.", 
          ephemeral: true 
        });
      }
      
      match.votes.team1.delete(playerId);
      match.votes.team2.delete(playerId);
      
      if (team === "1") {
        match.votes.team1.add(playerId);
      } else {
        match.votes.team2.add(playerId);
      }
      
      // Update or create 4fun vote status message
      await updateOrCreateVoteMessage(interaction.channel, match, true);
      
      const team1Votes = match.votes.team1.size;
      const team2Votes = match.votes.team2.size;
      
      if (team1Votes >= 6) {
        await interaction.channel.send(`🏆 **Team 1 has reached 6 votes! 4Fun Match ending...**`);
        await end4funMatch(interaction.channel, "1");
      } else if (team2Votes >= 6) {
        await interaction.channel.send(`🏆 **Team 2 has reached 6 votes! 4Fun Match ending...**`);
        await end4funMatch(interaction.channel, "2");
      } else {
        // Just acknowledge the vote
        await interaction.deferUpdate().catch(() => {});
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

    if (interaction.customId.startsWith("accept_duo_") || interaction.customId.startsWith("decline_duo_")) {
    const parts = interaction.customId.split('_');
    const action = parts[0]; // "accept" or "decline"
    const requesterId = parts[2];
    const targetId = parts[3];
    
    // Verify the request exists and the interacting user is the target
    const request = pendingDuoRequests.get(requesterId);
    if (!request || request.targetId !== targetId) {
        return interaction.reply({
            content: "❌ This duo request has expired or is invalid.",
            ephemeral: true
        });
    }
    
    if (interaction.user.id !== targetId) {
        return interaction.reply({
            content: "❌ Only the requested player can respond to this duo request.",
            ephemeral: true
        });
    }
    
    if (action === "accept") {
      // Form the duo partnership
      const requester = ensurePlayer(requesterId);
      const target = ensurePlayer(targetId);
        
      requester.fun.duoPartner = targetId;
      target.fun.duoPartner = requesterId;
      saveData();
        
      // Remove from pending requests
      pendingDuoRequests.delete(requesterId);
        
      // Update the message to show it was accepted
      const acceptedEmbed = EmbedBuilder.from(interaction.message.embeds[0])
        .setColor(0x00ff00)
        .spliceFields(3, 1, { name: "Status", value: "✅ Accepted", inline: true });
        
      await interaction.message.edit({ 
        embeds: [acceptedEmbed], 
        components: [] 
      });
        
      await interaction.reply({
        content: `✅ You have accepted the duo request from <@${requesterId}>! You are now duo partners.`,
        ephemeral: true
      });

      if (request.timer) {
        clearTimeout(request.timer);
      }

    } else {
        // Decline the request
        pendingDuoRequests.delete(requesterId);
        
        // Update the message to show it was declined
        const declinedEmbed = EmbedBuilder.from(interaction.message.embeds[0])
            .setColor(0xff0000)
            .spliceFields(3, 1, { name: "Status", value: "❌ Declined", inline: true });
        
        await interaction.message.edit({ 
            embeds: [declinedEmbed], 
            components: [] 
        });
        
        await interaction.reply({
            content: "❌ You have declined the duo request.",
            ephemeral: true
        });
        
        // Notify the requester
        try {
            const requesterUser = await client.users.fetch(requesterId);
            await requesterUser.send(`❌ <@${targetId}> declined your duo request.`);
        } catch (error) {
            // If DMs are disabled, that's okay
        }

        if (request.timer) {
          clearTimeout(request.timer);
        }
    }
  }

    if (interaction.customId === 'duo4fun') {
      const requesterId = interaction.user.id;
      const requester = ensurePlayer(requesterId);

      // Validation checks
      if (!requester.summonerName) {
          return interaction.reply({
              content: "❌ You must be registered with `!register` before requesting a duo.",
              ephemeral: true
          });
      }

      if (requester.fun.duoPartner) {
          return interaction.reply({
              content: `❌ You are already in a duo with <@${requester.fun.duoPartner}>. Use \`!duobreak\` to dissolve it first.`,
              ephemeral: true
          });
      }

      // Check for existing pending request
      if (pendingDuoRequests.has(requesterId)) {
          return interaction.reply({
              content: "❌ You already have a pending duo request. Please wait for it to be accepted or expire.",
              ephemeral: true
          });
      }

      // Create the user select menu with CORRECT method
      const selectMenuRow = new ActionRowBuilder()
          .addComponents(
              new UserSelectMenuBuilder()
                  .setCustomId('duo_partner_select')
                  .setPlaceholder('Select your duo partner...')
                  .setMaxValues(1) // ✅ CORRECTED: Use setMaxValues instead of setMaxUsers
          );

      await interaction.reply({
          content: 'Please select your duo partner from the list below:',
          components: [selectMenuRow],
          ephemeral: true
      });
    }

    // 4fun queue buttons
    if (interaction.customId === "join4fun") {
      const id = interaction.user.id;
      ensurePlayer(id);

      // Check if in timeout
      const timeoutStatus = isUserInTimeout(interaction.user.id);
      if (timeoutStatus.inTimeout) {
        const timeLeft = formatTimeLeft(timeoutStatus.timeLeft);
        return interaction.reply({
          content: `⏰ You are currently in a timeout penalty and cannot join the queue for ${timeLeft}.`,
          ephemeral: true,
        });
      }

      // Check if in any active match
      const isInAnyMatch = Array.from(matches.values()).some(match => 
        match.team1.includes(id) || match.team2.includes(id)
      ) || Array.from(matches4fun.values()).some(match => 
        match.team1.includes(id) || match.team2.includes(id)
      );
      
      if (isInAnyMatch) {
        return interaction.reply({
          content: "⚠️ You are currently in an active match and cannot join the queue until it ends.",
          ephemeral: true,
        });
      }

      if (!playerData[id].summonerName) {
        return interaction.reply({
          content: "❌ You must **register** first with !register <OP.GG link> before joining the 4fun queue.",
          ephemeral: true,
        });
      }

      if (queue4fun.includes(id)) {
        return interaction.reply({ content: "⚠️ You're already in the 4fun queue.", ephemeral: true });
      }

      if (queue4fun.length >= QUEUE4FUN_SIZE) {
        return interaction.reply({ 
          content: "⚠️ The 4fun queue is already full. Please wait for the next queue", 
          ephemeral: true 
        });
      }

      queue4fun.push(id);
      saveData();
      await update4funQueueMessage();
      
      if (queue4fun.length === QUEUE4FUN_SIZE && !active4funReadyCheck) {
        await start4funReadyCheck(interaction.channel);
      }
      
      await interaction.deferUpdate().catch(err => { 
        if (err.code !== 10062) console.error("4fun deferUpdate failed:", err); 
      });
    }

    else if (interaction.customId === "leave4fun") {
      const id = interaction.user.id;
      
      if (!queue4fun.includes(id)) {
        try {
          await interaction.deferUpdate();
        } catch (err) {
          if (err.code !== 10062) console.error("4fun Leave deferUpdate failed:", err);
        }
        return;
      }

      queue4fun = queue4fun.filter((x) => x !== id);
      saveData();
      await update4funQueueMessage();

      try {
        await interaction.deferUpdate();
      } catch (err) {
        if (err.code !== 10062) console.error("4fun Leave deferUpdate failed:", err);
      }
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
  if (message.channel.name === 'queue' || message.channel.name === '4fun-queue') {
    // Don't delete bot messages that are part of ready checks or other important bot messages
    if (message.embeds.length > 0) {
      const embed = message.embeds[0];
      if (embed.title && (
        embed.title.includes("Ready Check") || 
        embed.title.includes("Current Queue") ||
        embed.title.includes("4Fun Queue")
      )) {
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
    
    // 4fun force ready command
    if (cmd === "!4funforceready") {
      if (!message.member.permissions.has("ManageGuild")) {
        return message.reply("❌ Only staff members can use this command.");
      }

      if (!queue4fun || queue4fun.length < QUEUE4FUN_SIZE) {
        return message.reply("⚠️ There isn't an active 4fun ready check right now.");
      }

      message.channel.send("✅ 4Fun Force-ready activated — all players are now marked ready!");

      if (active4funReadyCheck && active4funReadyCheck.collector) {
        try {
          const curMsg = active4funReadyCheck.msg;
          try {
            const infoEmbed = EmbedBuilder.from(curMsg.embeds?.[0] || embed)
              .setDescription("✅ 4Fun Force-ready activated by staff. Match is starting!")
              .setColor(0x00ff00);
            await curMsg.edit({ embeds: [infoEmbed], components: [] }).catch(() => {});
          } catch (e) { }

          active4funReadyCheck.collector.stop("all_ready");
        } catch (err) {
          console.error("Error stopping active 4fun ready check:", err);
          await make4funTeams(message.channel);
        }
      } else {
        await make4funTeams(message.channel);
      }
    }

    // 4fun end match command
    if (cmd === "!4funendmatch") {
      if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
        return message.reply("❌ Only staff members can use this command.");
      }
      
      const team = args[0];
      if (!team || (team !== "1" && team !== "2")) {
        return message.reply("Usage: !4funendmatch <1|2>");
      }
      
      end4funMatch(message.channel, team);
    }

    // ---------------- !mystreak ----------------
    if (cmd === "!mystreak") {
      const userMention = args[0] || message.author.id;
      const userId = userMention.replace(/[<@!>]/g, "") || message.author.id;
      
      const player = ensurePlayer(userId);
      
      let streakMessage = "";
      if (player.streakType === "win") {
        streakMessage = `🔥 You are on a **${player.currentStreak} game win streak**!\n`;;
      } else if (player.streakType === "loss") {
        streakMessage = `😔 You are on a **${Math.abs(player.currentStreak)} game loss streak**.\n`;
      } else {
        streakMessage = "📊 You have no active win or loss streak.\n";
      }
      
      const embed = new EmbedBuilder()
        .setTitle("📊 Your Current Streak")
        .setDescription(streakMessage)
        .addFields(
          { name: "Wins", value: `${player.wins}`, inline: true },
          { name: "Losses", value: `${player.losses}`, inline: true },
          { name: "Win Rate", value: player.wins + player.losses > 0 ? `${((player.wins / (player.wins + player.losses)) * 100).toFixed(1)}%` : "0%", inline: true }
        )
        .setColor(player.streakType === "win" ? 0x00ff00 : player.streakType === "loss" ? 0xff0000 : 0x888888)
        .setTimestamp();
      
      await message.channel.send({ embeds: [embed] });
    }

    // ---------------- !adjustlp (STAFF ONLY) ----------------
    if (cmd === "!adjustlp") {
      if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
        return message.reply("❌ Only staff members can use this command.");
      }

      if (args.length < 2) {
        return message.reply("Usage: !adjustlp <@user> <amount>\nUse positive number to add LP, negative to subtract LP\nExample: `!adjustlp @user 25` or `!adjustlp @user -15`");
      }

      const userMention = args[0];
      const lpAmount = parseInt(args[1]);
      
      if (isNaN(lpAmount)) {
        return message.reply("❌ Please provide a valid number for LP amount.");
      }

      const userId = userMention.replace(/[<@!>]/g, "");
      const player = ensurePlayer(userId);
      
      if (!player.summonerName) {
        return message.reply("❌ That user is not registered. They need to use `!register` first.");
      }

      // Store old stats for display
      const oldRank = player.rank;
      const oldDivision = player.division;
      const oldLP = player.lp;
      const oldIHP = getIHP(player);

      // Adjust LP
      player.lp += lpAmount;

      // Ensure LP doesn't go negative
      if (player.lp < 0) {
        player.lp = 0;
      }

      // Update rank based on new IHP
      const newIHP = getIHP(player);
      const newStats = IHPToRank(newIHP);
      
      player.rank = newStats.rank;
      player.division = newStats.division;
      player.lp = newStats.lp;

      saveData();
      await updateLeaderboardChannel(message.guild);

      const action = lpAmount >= 0 ? "added" : "subtracted";
      const lpDisplay = Math.abs(lpAmount);
      
      const embed = new EmbedBuilder()
        .setTitle("📊 LP Adjustment")
        .setDescription(`LP ${action} for <@${userId}>`)
        .addFields(
          { name: "LP Change", value: `${lpAmount >= 0 ? '+' : ''}${lpAmount} LP`, inline: true },
          { name: "Old Rank", value: formatRankDisplay(oldRank, oldDivision, oldLP), inline: true },
          { name: "New Rank", value: formatRankDisplay(player.rank, player.division, player.lp), inline: true },
          { name: "Old IHP", value: oldIHP.toString(), inline: true },
          { name: "New IHP", value: newIHP.toString(), inline: true }
        )
        .setColor(lpAmount >= 0 ? 0x00ff00 : 0xff0000)
        .setTimestamp()
        .setFooter({ text: `Adjusted by ${message.author.username}` });

      await message.channel.send({ embeds: [embed] });
    }

    // ---------------- !adjustrecord (STAFF ONLY) ----------------
    if (cmd === "!adjustrecord") {
      if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
        return message.reply("❌ Only staff members can use this command.");
      }

      if (args.length < 3) {
        return message.reply("Usage: !adjustrecord <@user> <wins> <losses>\nExample: `!adjustrecord @user 5 3` to set wins=5, losses=3");
      }

      const userMention = args[0];
      const newWins = parseInt(args[1]);
      const newLosses = parseInt(args[2]);
      
      if (isNaN(newWins) || isNaN(newLosses) || newWins < 0 || newLosses < 0) {
        return message.reply("❌ Please provide valid positive numbers for wins and losses.");
      }

      const userId = userMention.replace(/[<@!>]/g, "");
      const player = ensurePlayer(userId);
      
      if (!player.summonerName) {
        return message.reply("❌ That user is not registered. They need to use `!register` first.");
      }

      // Store old stats for display
      const oldWins = player.wins || 0;
      const oldLosses = player.losses || 0;
      const oldRank = player.rank;
      const oldDivision = player.division;
      const oldLP = player.lp;

      // Update wins and losses
      player.wins = newWins;
      player.losses = newLosses;

      // Update streak logic based on new record
      const totalGames = newWins + newLosses;
      if (totalGames === 0) {
        player.currentStreak = 0;
        player.streakType = "none";
      } else {
        // Simple streak logic: if last change was positive, assume win streak
        if (newWins > oldWins) {
          player.currentStreak = Math.max(1, player.currentStreak >= 0 ? player.currentStreak + 1 : 1);
          player.streakType = "win";
        } else if (newLosses > oldLosses) {
          player.currentStreak = Math.min(-1, player.currentStreak <= 0 ? player.currentStreak - 1 : -1);
          player.streakType = "loss";
        }
        // If wins/losses were set manually without clear "last game", reset to no streak
        else {
          player.currentStreak = 0;
          player.streakType = "none";
        }
      }

      saveData();
      await updateLeaderboardChannel(message.guild);

      const totalGamesNew = newWins + newLosses;
      const winRateNew = totalGamesNew > 0 ? ((newWins / totalGamesNew) * 100).toFixed(1) : "0.0";
      const winRateOld = (oldWins + oldLosses) > 0 ? ((oldWins / (oldWins + oldLosses)) * 100).toFixed(1) : "0.0";

      const embed = new EmbedBuilder()
        .setTitle("📊 Record Adjustment")
        .setDescription(`Win/Loss record updated for <@${userId}>`)
        .addFields(
          { 
            name: "Old Record", 
            value: `${oldWins}W ${oldLosses}L (${winRateOld}% WR)`, 
            inline: true 
          },
          { 
            name: "New Record", 
            value: `${newWins}W ${newLosses}L (${winRateNew}% WR)`, 
            inline: true 
          },
          { 
            name: "Net Change", 
            value: `${newWins - oldWins >= 0 ? '+' : ''}${newWins - oldWins}W / ${newLosses - oldLosses >= 0 ? '+' : ''}${newLosses - oldLosses}L`, 
            inline: true 
          }
        )
        .setColor(0x0099FF)
        .setTimestamp()
        .setFooter({ text: `Adjusted by ${message.author.username}` });

      await message.channel.send({ embeds: [embed] });
    }

    // ---------------- !addwin / !addloss (STAFF ONLY) ----------------
    if (cmd === "!addwin" || cmd === "!addloss") {
      if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
        return message.reply("❌ Only staff members can use this command.");
      }

      if (args.length < 1) {
        return message.reply(`Usage: !${cmd} <@user> [lp_change]\nExample: !${cmd} @user 20`);
      }

      const userMention = args[0];
      const lpChange = args[1] ? parseInt(args[1]) : 20; // Default 20 LP change

      if (args[1] && isNaN(lpChange)) {
        return message.reply("❌ Please provide a valid number for LP change.");
      }

      const userId = userMention.replace(/[<@!>]/g, "");
      const player = ensurePlayer(userId);
      
      if (!player.summonerName) {
        return message.reply("❌ That user is not registered. They need to use `!register` first.");
      }

      // Store old stats for display
      const oldWins = player.wins || 0;
      const oldLosses = player.losses || 0;
      const oldRank = player.rank;
      const oldDivision = player.division;
      const oldLP = player.lp;
      const oldIHP = getIHP(player);

      const isWin = cmd === "!addwin";
      
      if (isWin) {
        // Add win
        player.wins++;
        
        // Update streak
        if (player.streakType === "win") {
          player.currentStreak++;
        } else {
          player.currentStreak = 1;
          player.streakType = "win";
        }
        
        // Add LP
        player.lp += lpChange;
      } else {
        // Add loss
        player.losses++;
        
        // Update streak
        if (player.streakType === "loss") {
          player.currentStreak--;
        } else {
          player.currentStreak = -1;
          player.streakType = "loss";
        }
        
        // Subtract LP (but don't go below 0)
        player.lp = Math.max(0, player.lp - lpChange);
      }

      // Update rank based on new IHP
      const newIHP = getIHP(player);
      const newStats = IHPToRank(newIHP);
      
      player.rank = newStats.rank;
      player.division = newStats.division;
      player.lp = newStats.lp;

      saveData();
      await updateLeaderboardChannel(message.guild);

      const resultType = isWin ? "Win" : "Loss";
      const lpDisplay = isWin ? `+${lpChange}` : `-${lpChange}`;
      
      const embed = new EmbedBuilder()
        .setTitle(`🎮 ${resultType} Added`)
        .setDescription(`${resultType} added for <@${userId}>`)
        .addFields(
          { name: "LP Change", value: `${lpDisplay} LP`, inline: true },
          { name: "Old Record", value: `${oldWins}W ${oldLosses}L`, inline: true },
          { name: "New Record", value: `${player.wins}W ${player.losses}L`, inline: true },
          { name: "Old Rank", value: formatRankDisplay(oldRank, oldDivision, oldLP), inline: true },
          { name: "New Rank", value: formatRankDisplay(player.rank, player.division, player.lp), inline: true },
          { name: "Current Streak", value: player.currentStreak > 0 ? `${player.currentStreak} win streak` : player.currentStreak < 0 ? `${Math.abs(player.currentStreak)} loss streak` : "No streak", inline: true }
        )
        .setColor(isWin ? 0x00ff00 : 0xff0000)
        .setTimestamp()
        .setFooter({ text: `Added by ${message.author.username}` });

      await message.channel.send({ embeds: [embed] });
    }

    // ---------------- !smurfing (STAFF ONLY) ----------------
    if (cmd === "!smurfing") {
      if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
        return message.reply("❌ Only staff members can use this command.");
      }
      
      // In your !smurfing command, add this right after the staff permission check:
      if (!playerData._smurfRefunds) {
          playerData._smurfRefunds = {
              processedMatches: new Set(),
              processedSmurfs: new Set(),
              refundHistory: {}
          };
      }

      // Ensure processedSmurfs is a Set
      if (!(playerData._smurfRefunds.processedSmurfs instanceof Set)) {
          playerData._smurfRefunds.processedSmurfs = new Set(playerData._smurfRefunds.processedSmurfs || []);
      }

      // Ensure processedMatches is a Set  
      if (!(playerData._smurfRefunds.processedMatches instanceof Set)) {
          playerData._smurfRefunds.processedMatches = new Set(playerData._smurfRefunds.processedMatches || []);
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
        const matchHistory = await loadMatchHistory();
        
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
      if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
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
    if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
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
    if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
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
    if (cmd === "!queueban") {
      if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
        return message.reply("❌ Only staff members can use this command.");
      }

      const userMention = args[0];
      if (!userMention) return message.reply("Usage: !queueban <@user>");

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
    if (cmd === "!queueunban") {
      if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
        return message.reply("❌ Only staff members can use this command.");
      }

      const userMention = args[0];
      if (!userMention) return message.reply("Usage: !queueunban <@user>");

      const userId = userMention.replace(/[<@!>]/g, "");

      if (!bannedUsers.has(userId)) {
        return message.reply("⚠️ That user is not currently banned.");
      }

      bannedUsers.delete(userId);
      saveData();

      message.channel.send(`✅ <@${userId}> has been **unbanned** and can queue again.`);
    }

  if (cmd === "!remove") {
    if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
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
    if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
      return message.reply("❌ Only staff members can use this command.");
    }

    // Get the match for this specific channel
    const match = matches.get(message.channel.id);
    if (!match) {
      return message.reply("❌ There is no active match in this channel to cancel.");
    }

    const guild = message.guild;

    try {
      console.log("🛑 Starting match cancellation...");
      
      // CRITICAL: Remove this match from active matches FIRST to prevent further issues
      matches.delete(message.channel.id);
      console.log("✅ Removed match from active matches");

      // CRITICAL: Remove all players from this match so they can queue again
      const allPlayers = [...(match.team1 || []), ...(match.team2 || [])];
      console.log(`🔄 Clearing ${allPlayers.length} players from match`);

      // Clear players from queue if they're stuck there
      let clearedFromQueue = 0;
      for (const playerId of allPlayers) {
        const index = queue.indexOf(playerId);
        if (index > -1) {
          queue.splice(index, 1);
          clearedFromQueue++;
        }
      }
      console.log(`✅ Cleared ${clearedFromQueue} players from queue`);

      saveData();
      await updateQueueMessage();

      // Delete the specific channels for THIS match only
      const deletePromises = [];
      
      // Delete the exact voice channels from match data (not by name)
      if (match.team1VC) {
        deletePromises.push(match.team1VC.delete().catch(err => {
          console.log(`Could not delete team1 voice channel: ${err.message}`);
        }));
      }
      
      if (match.team2VC) {
        deletePromises.push(match.team2VC.delete().catch(err => {
          console.log(`Could not delete team2 voice channel: ${err.message}`);
        }));
      }
      
      // Delete the match text channel (the current channel)
      if (match.matchChannel) {
        deletePromises.push(match.matchChannel.delete().catch(err => {
          console.log(`Could not delete match channel: ${err.message}`);
        }));
      }
      
      // Delete the category LAST (after all children are deleted)
      if (match.matchCategory) {
        deletePromises.push(match.matchCategory.delete().catch(err => {
          console.log(`Could not delete match category: ${err.message}`);
        }));
      }

      // Wait for all deletions to complete
      await Promise.allSettled(deletePromises);

      await message.channel.send("🛑 The current match has been canceled. Players have been cleared from the queue and match channels have been deleted.");
      
    } catch (err) {
      console.error("Error in cancelmatch:", err);
      
      // Even if there's an error, make sure the match is cleared
      // Clean up vote timers
      cleanupVoteTimers(message.channel.id);
      matches.delete(message.channel.id);
      saveData();
      await updateQueueMessage();
      
      await message.channel.send("⚠️ Match canceled with some errors, but players have been cleared from the queue.");
    }
  }

  // ---------------- !duobreak ----------------
  if (cmd === "!duobreak") {
      const playerId = message.author.id;
      const player = ensurePlayer(playerId);

      if (!player.fun.duoPartner) {
          return message.reply("❌ You are not in a duo partnership.");
      }

      const partnerId = player.fun.duoPartner;
      const partner = ensurePlayer(partnerId);

      // Remove from queue if either is queued
      if (queue4fun.includes(playerId)) {
          queue4fun = queue4fun.filter(id => id !== playerId);
      }
      if (queue4fun.includes(partnerId)) {
          queue4fun = queue4fun.filter(id => id !== partnerId);
      }

      // Break the duo
      player.fun.duoPartner = null;
      partner.fun.duoPartner = null;
      
      saveData();
      await update4funQueueMessage();

      await message.reply(`✅ Duo partnership with <@${partnerId}> has been dissolved.`);
  }

  // ---------------- !duostatus ----------------
  if (cmd === "!duostatus") {
      const userMention = args[0] || message.author.id;
      const userId = userMention.replace(/[<@!>]/g, "") || message.author.id;
      
      const player = ensurePlayer(userId);
      const isSelf = userId === message.author.id;

      if (!player.fun.duoPartner) {
          const messageText = isSelf ? 
              "You are not currently in a duo partnership. Click the '🤝 Request Duo' button in the 4fun queue to form one." :
              `<@${userId}> is not in a duo partnership.`;
          return message.reply(messageText);
      }

      const partner = ensurePlayer(player.fun.duoPartner);
      const partnerInQueue = queue4fun.includes(player.fun.duoPartner);
      const playerInQueue = queue4fun.includes(userId);

      const embed = new EmbedBuilder()
          .setTitle("🤝 Duo Status")
          .setDescription(isSelf ? 
              `You are duo partners with <@${player.fun.duoPartner}>` :
              `<@${userId}> is duo partners with <@${player.fun.duoPartner}>`)
          .addFields(
              { name: "Duo Partner", value: `<@${player.fun.duoPartner}>`, inline: true },
              { name: "Queue Status", value: playerInQueue && partnerInQueue ? "✅ Both in queue" : playerInQueue ? "🟡 You in queue" : partnerInQueue ? "🟡 Partner in queue" : "❌ Neither in queue", inline: true }
          )
          .setColor(0x0099FF)
          .setTimestamp();

      await message.channel.send({ embeds: [embed] });
  }

  // ---------------- !simulate4fun ----------------
  if (cmd === "!simulate4fun") {
      if (!message.member.permissions.has("ManageGuild")) {
          return message.reply("❌ Only staff members can use this command.");
      }

      const count = parseInt(args[0] || "10");
      
      // Get registered players with summoner names (no role requirements for 4fun)
      const eligiblePlayers = Object.keys(playerData).filter(id => {
          // Filter out system keys
          if (id.startsWith('_')) return false;
          
          const player = playerData[id];
          
          // Check for summoner name only (no role requirements for 4fun)
          if (!player?.summonerName) return false;
          
          return true;
      });

      if (eligiblePlayers.length === 0) {
          return message.reply("❌ No registered players found.");
      }

      // Clear current 4fun queue first
      queue4fun = [];
      
      // Shuffle eligible players array to get random selection
      const shuffledPlayers = [...eligiblePlayers].sort(() => Math.random() - 0.5);
      
      // Add random players to 4fun queue (up to the requested count)
      const playersToAdd = Math.min(count, shuffledPlayers.length);
      let addedCount = 0;

      for (let i = 0; i < playersToAdd; i++) {
          const playerId = shuffledPlayers[i];
          
          // Additional safety check
          const player = playerData[playerId];
          if (player.summonerName) {
              if (!queue4fun.includes(playerId)) {
                  queue4fun.push(playerId);
                  addedCount++;
              }
          }
      }

      saveData();
      
      let response = `🎉 Randomly added ${addedCount} players to 4fun queue. 4Fun Queue = ${queue4fun.length}/${QUEUE4FUN_SIZE}`;

      if (addedCount < count) {
          response += `\nℹ️ Only ${eligiblePlayers.length} registered players available.`;
      }

      // Show which players were added
      const addedPlayerMentions = queue4fun.map(id => `<@${id}>`).join(', ');
      response += `\n\n**Players added:** ${addedPlayerMentions}`;
      
      message.channel.send(response);
      await update4funQueueMessage();

      // Start 4fun ready check if queue becomes full
      if (queue4fun.length === QUEUE4FUN_SIZE && !active4funReadyCheck) {
          await start4funReadyCheck(message.channel);
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
    if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
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
  if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
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
    if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
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
    if (!message.member.permissions.has(PermissionsBitField.Flags.ManageMessages)) {
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
    const matchHistory = await loadMatchHistory();
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
    const matchHistory = await loadMatchHistory();
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

  if (cmd === "!recentmatches") {
    if (!message.member.permissions.has("ManageGuild")) {
      return message.reply("❌ Only staff members can use this command.");
    }

    const matchHistory = await loadMatchHistory();
    const recentMatches = matchHistory.slice(-10).reverse(); // Get 10 most recent matches

    if (recentMatches.length === 0) {
      return message.reply("❌ No match history found.");
    }

    const matchList = recentMatches.map(match => {
      const date = new Date(match.timestamp).toLocaleDateString();
      const status = match.voided ? "❌ VOIDED" : "✅ ACTIVE";
      
      // Calculate average ELO BEFORE the match using oldIHP values
      let team1PreMatchAvg = "N/A";
      let team2PreMatchAvg = "N/A";
      
      if (match.eloChanges && match.eloChanges.length > 0) {
        // Get team1 players' old IHP (before match)
        const team1PreMatchIHP = match.team1.map(playerId => {
          const playerChange = match.eloChanges.find(change => change.id === playerId);
          return playerChange ? playerChange.oldIHP : 0;
        }).filter(ihp => ihp > 0);
        
        // Get team2 players' old IHP (before match)
        const team2PreMatchIHP = match.team2.map(playerId => {
          const playerChange = match.eloChanges.find(change => change.id === playerId);
          return playerChange ? playerChange.oldIHP : 0;
        }).filter(ihp => ihp > 0);
        
        // Calculate averages
        if (team1PreMatchIHP.length > 0) {
          team1PreMatchAvg = Math.round(team1PreMatchIHP.reduce((a, b) => a + b, 0) / team1PreMatchIHP.length);
        }
        if (team2PreMatchIHP.length > 0) {
          team2PreMatchAvg = Math.round(team2PreMatchIHP.reduce((a, b) => a + b, 0) / team2PreMatchIHP.length);
        }
      }
      
      return `**${match.id}** - ${date} - Team ${match.winner} won - 🔵 ${team1PreMatchAvg} | 🔴 ${team2PreMatchAvg} - ${status}`;
    }).join('\n');

    const embed = new EmbedBuilder()
      .setTitle("📜 Recent Matches")
      .setDescription(matchList)
      .setFooter({ text: "Shows average ELO before the match was scored" })
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

    const matchHistory = await loadMatchHistory();
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
  
  // ADDED: Enhanced combination search that considers role preferences
  let bestTeam1 = null;
  let bestTeam2 = null;
  let bestDiff = Infinity;
  let bestRoleScore = Infinity;
  let bestAvg1 = 0;
  let bestAvg2 = 0;
  let usedRoleOptimization = false;

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

  console.log(`🔍 Starting enhanced team combination search for ${players.length} players`);
  console.log(`🎯 Considering role preferences with 25 Elo tolerance`);
  
  // Generate all possible team combinations
  const allTeam1Combinations = generateCombinations(players, 5);
  
  console.log(`📊 Evaluating ${allTeam1Combinations.length} possible team combinations`);
  
  // First pass: Find all combinations within 25 Elo difference
  const viableCombinations = [];
  
  for (const team1 of allTeam1Combinations) {
    const team2 = players.filter(player => !team1.includes(player));
    
    // Calculate average ELO for both teams
    const sum1 = team1.reduce((sum, id) => sum + getIHP(ensurePlayer(id)), 0);
    const sum2 = team2.reduce((sum, id) => sum + getIHP(ensurePlayer(id)), 0);
    const avg1 = sum1 / 5;
    const avg2 = sum2 / 5;
    const diff = Math.abs(avg1 - avg2);
    
    // Check if within 25 Elo tolerance
    if (diff <= 25) {
      viableCombinations.push({ team1, team2, diff, avg1, avg2 });
    }
  }

  console.log(`📈 Found ${viableCombinations.length} combinations within 25 Elo tolerance`);

  // If we have viable combinations within 50 Elo, choose the one with best role assignment
  if (viableCombinations.length > 0) {
    console.log(`🎯 Selecting best team based on role preferences from ${viableCombinations.length} viable options`);
    usedRoleOptimization = true;
    
    for (const { team1, team2, diff, avg1, avg2 } of viableCombinations) {
      // Assign roles and calculate role satisfaction
      const team1Roles = assignRoles(team1);
      const team2Roles = assignRoles(team2);
      
      const team1Satisfaction = calculateTeamSatisfaction(team1, team1Roles);
      const team2Satisfaction = calculateTeamSatisfaction(team2, team2Roles);
      
      // Calculate total role score (lower is better)
      const totalRoleScore = team1Satisfaction.totalPoints + team2Satisfaction.totalPoints;
      
      // Update best combination if this one has better role assignment
      if (totalRoleScore < bestRoleScore || 
          (totalRoleScore === bestRoleScore && diff < bestDiff)) {
        bestRoleScore = totalRoleScore;
        bestDiff = diff;
        bestTeam1 = team1;
        bestTeam2 = team2;
        bestAvg1 = avg1;
        bestAvg2 = avg2;
      }
    }
    
    console.log(`✅ Selected team with Elo diff: ${bestDiff.toFixed(2)} and role score: ${bestRoleScore}`);
    
  } else {
    // Fallback to original Elo-based matching if no combinations within 50 Elo
    console.log(`⚠️ No teams found within 50 Elo tolerance, falling back to pure Elo balancing`);
    
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
    
    console.log(`✅ Best fallback team combination found with ELO difference: ${bestDiff.toFixed(2)}`);
  }

  console.log(`🔵 Team 1 Avg ELO: ${bestAvg1.toFixed(2)}, 🔴 Team 2 Avg ELO: ${bestAvg2.toFixed(2)}`);
  console.log(`🎯 Role optimization ${usedRoleOptimization ? 'APPLIED' : 'NOT APPLIED'} (within 50 Elo tolerance)`);

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

  // Enhanced console logging with role optimization info
  console.log('\n🎯 ===== ENHANCED ROLE ASSIGNMENT ANALYTICS =====');
  console.log(`📅 Match created at: ${new Date().toLocaleString()}`);
  console.log(`⚖️  Elo Balance: ${bestDiff.toFixed(2)} ${usedRoleOptimization ? '(with role optimization)' : '(pure Elo balance)'}`);
  
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
  console.log(`  Role Optimization: ${usedRoleOptimization ? 'APPLIED ✅' : 'NOT APPLIED ⚠️'}`);
  console.log('🎯 ===== END ENHANCED ROLE ASSIGNMENT =====\n');

  // Rest of the function remains the same...
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
  
  const matchId = await getNextMatchId();
  const matchCategoryName = `Match ${matchId}`; // Simpler name without timestamp
  
  // Create a dedicated category for this match
  const matchCategory = await guild.channels.create({ 
    name: matchCategoryName, 
    type: 4, // Category type
    permissionOverwrites: [
      {
        id: guild.id, // @everyone
        deny: ['ViewChannel'] // CHANGE: Allow everyone to view instead of deny
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
        deny: ['ViewChannel']
      },
      // Allow match participants to view and send messages
      ...bestTeam1.map(playerId => ({
        id: playerId,
        type: 1,
        deny: ['ViewChannel', 'SendMessages', 'ReadMessageHistory'],
      })),
      ...bestTeam2.map(playerId => ({
        id: playerId,
        type: 1,
        deny: ['ViewChannel', 'SendMessages', 'ReadMessageHistory'],
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
        deny: ['ViewChannel', 'Connect'], // Everyone can see the channel
        /*deny: ['Speak'], // Mute spectators/other team*/
      },
      ...bestTeam1.map(playerId => ({
        id: playerId,
        type: 1,
        deny: ['ViewChannel', 'Connect', 'Speak']
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
        deny: ['ViewChannel', 'Connect'], // Everyone can see the channel
        /*deny: ['Speak'], // Mute spectators/other team*/
      },
      ...bestTeam2.map(playerId => ({
        id: playerId,
        type: 1,
        deny: ['ViewChannel', 'Connect', 'Speak']
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
  let draftSuccess = false;
  let draftLinks = {
    blue: "https://draftlol.dawe.gg",
    red: "https://draftlol.dawe.gg", 
    spectator: "https://draftlol.dawe.gg",
  };

  try {
    console.log("🔄 Starting draft lobby creation...");
    const generatedLinks = await createDraftLolLobby(); // Store in a different variable
    draftLinks = generatedLinks; // Then assign to draftLinks
    draftSuccess = true;
    console.log(`✅ Draft links generated successfully`);
    console.log(`🔵 Stored Blue: ${draftLinks.blue}`);
    console.log(`🔴 Stored Red: ${draftLinks.red}`);
    console.log(`👁️ Stored Spectator: ${draftLinks.spectator}`);
  } catch (err) {
    console.error("❌ Critical error creating draft lobby:", err);
    draftSuccess = false;
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
    blue: draftLinks.blue,
    red: draftLinks.red,
    spectator: draftLinks.spectator,
    matchId: matchId,
    matchMessageId: null,
    votes: {
      team1: new Set(),
      team2: new Set()
    },
    // ✅ Add drafters info here instead
    drafters: draftSuccess ? {
      blue: team1Sorted[0], // Highest Elo blue player
      red: team2Sorted[0]   // Highest Elo red player
    } : null
  };

  // Debug: Log what's actually being stored in matchData
  console.log(`🔍 FINAL MATCH DATA DRAFT LINKS:`);
  console.log(`🔵 Match Blue: ${matchData.blue}`);
  console.log(`🔴 Match Red: ${matchData.red}`);
  console.log(`👁️ Match Spectator: ${matchData.spectator}`);

  // Build components based on draft success
  const components = [];

  if (draftSuccess) {
    // Get highest Elo players for each team
    const team1HighestElo = team1Sorted[0];
    const team2HighestElo = team2Sorted[0];
    
    // Store drafters in match data
    matchData.drafters = {
      blue: team1HighestElo,
      red: team2HighestElo
    };

    // Change from Link buttons to regular buttons with custom IDs
    const blueDraftButton = new ButtonBuilder()
      .setCustomId('blue_draft')
      .setLabel('🟦 Blue Team Draft')
      .setStyle(ButtonStyle.Primary);

    const redDraftButton = new ButtonBuilder()
      .setCustomId('red_draft')  
      .setLabel('🔴 Red Team Draft')
      .setStyle(ButtonStyle.Danger);

    const spectatorButton = new ButtonBuilder()
      .setCustomId('spectator_draft')
      .setLabel('👁️ Spectator View')
      .setStyle(ButtonStyle.Secondary);

    const teamRow = new ActionRowBuilder().addComponents(
      blueDraftButton,
      redDraftButton,
      spectatorButton
    );

    components.push(teamRow);
  }

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

  components.push(managementRow);

  // Create embed description based on draft success
  let embedDescription = "";
  if (draftSuccess) {
    const team1HighestElo = team1Sorted[0];
    const team2HighestElo = team2Sorted[0];
    
    embedDescription = `**Assigned Drafters:**\n` +
      `🔵 Blue Team: <@${team1HighestElo}> (Highest Elo)\n` +
      `🔴 Red Team: <@${team2HighestElo}> (Highest Elo)\n\n` +
      `**Team OP.GG Links:**\n` +
      `[🔵 Blue Team Multi OP.GG](${team1Link})\n` +
      `[🔴 Red Team Multi OP.GG](${team2Link})\n\n` +
      `**Draft Access:**\n` +
      `• Team draft links: Assigned drafters + Staff only\n` +
      `• Spectator link: Anyone in server\n\n` +
      `**After match, vote with Team Won buttons - 6/10 votes needed**`;
  } else {
    embedDescription = `**Team OP.GG Links:**\n` +
      `[🔵 Blue Team Multi OP.GG](${team1Link})\n` +
      `[🔴 Red Team Multi OP.GG](${team2Link})\n\n` +
      `**After match, vote with Team Won buttons - 6/10 votes needed**`;
  }

  const matchEmbed = new EmbedBuilder()
    .setTitle("🎮 Match Lobby")
    .setDescription(embedDescription)
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

  const messageOptions = {
    embeds: [matchEmbed],
    components: components
  };

  // Only add content if draft links failed
  if (!draftSuccess) {
    messageOptions.content = `❌ Failed to create draft lobby. Players will need to make draft at https://draftlol.dawe.gg/ manually.`;
  }

  // Send the message
  const matchMessage = await matchChannel.send(messageOptions);

  // Store the match message ID for later reference
  matchData.matchMessageId = matchMessage.id;

  // Store match by channel ID
  matches.set(matchChannel.id, matchData);

  queue = [];
  startVoteMessageFloodMonitoring(matchChannel, matchData, false);
  saveData();
  updateQueueMessage();
}

async function make4funTeams(channel) {
  trackRequest();
  
  const players = [...queue4fun];
  
  // Initialize hidden MMR for new players based on their main rank
  players.forEach(playerId => {
    const player = ensurePlayer(playerId);
    if (player.fun.hiddenMMR === 0 && player.summonerName) {
      // Set initial hidden MMR based on main rank IHP
      player.fun.hiddenMMR = getIHP(player);
    }
  });

  let bestTeam1 = null;
  let bestTeam2 = null;
  let bestDiff = Infinity;
  let bestAvg1 = 0;
  let bestAvg2 = 0;

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

  console.log(`🔍 Starting 4fun team combination search for ${players.length} players`);
  const allTeam1Combinations = generateCombinations(players, 5);
  
  console.log(`📊 Evaluating ${allTeam1Combinations.length} possible 4fun team combinations`);
  
  for (const team1 of allTeam1Combinations) {
    const team2 = players.filter(player => !team1.includes(player));
    
    // Calculate average hidden MMR for both teams
    const sum1 = team1.reduce((sum, id) => sum + ensurePlayer(id).fun.hiddenMMR, 0);
    const sum2 = team2.reduce((sum, id) => sum + ensurePlayer(id).fun.hiddenMMR, 0);
    const avg1 = sum1 / 5;
    const avg2 = sum2 / 5;
    const diff = Math.abs(avg1 - avg2);
    
    if (diff < bestDiff) {
      bestDiff = diff;
      bestTeam1 = team1;
      bestTeam2 = team2;
      bestAvg1 = avg1;
      bestAvg2 = avg2;
    }
    
    if (bestDiff === 0) break;
  }

  console.log(`✅ Best 4fun team combination found with MMR difference: ${bestDiff.toFixed(2)}`);
  console.log(`🔵 Team 1 Avg MMR: ${bestAvg1.toFixed(2)}, 🔴 Team 2 Avg MMR: ${bestAvg2.toFixed(2)}`);

  const guild = channel.guild;
  const matchId = await getNextMatchId();
  const matchCategoryName = `4Fun Match ${matchId}`;

  const matchCategory = await guild.channels.create({ 
    name: matchCategoryName, 
    type: 4,
    permissionOverwrites: [
      {
        id: guild.id,
        allow: ['ViewChannel']
      }
    ]
  });

  const matchChannel = await guild.channels.create({ 
    name: "4fun-match-lobby", 
    type: 0, 
    parent: matchCategory.id,
    permissionOverwrites: [
      {
        id: guild.id,
      },
      ...bestTeam1.map(playerId => ({
        id: playerId,
        type: 1,
        allow: ['ViewChannel', 'SendMessages', 'ReadMessageHistory'],
      })),
      ...bestTeam2.map(playerId => ({
        id: playerId,
        type: 1,
        allow: ['ViewChannel', 'SendMessages', 'ReadMessageHistory'],
      }))
    ]
  });

  const team1VC = await guild.channels.create({ 
    name: "🔵 Team 1 (Blue)", 
    type: 2, 
    parent: matchCategory.id,
    permissionOverwrites: [
      {
        id: guild.id,
        allow: ['ViewChannel', 'Connect'],
        deny: ['Speak'],
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
        id: guild.id,
        allow: ['ViewChannel', 'Connect'],
        deny: ['Speak'],
      },
      ...bestTeam2.map(playerId => ({
        id: playerId,
        type: 1,
        allow: ['ViewChannel', 'Connect', 'Speak']
      }))
    ]
  });

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

  // Format team display with normal ranks instead of 4fun points
  function formatTeamDisplay(team) {
    return team
      .map((id) => {
        const player = playerData[id];
        const rankDisplay = formatRankDisplay(player.rank, player.division, player.lp);
        const funPoints = player.fun.points;
        return `<@${id}> / ${rankDisplay} (${funPoints} 4fun pts)`;
      })
      .join("\n");
  }

  let draftSuccess = false;
  let draftLinks = {
    blue: "https://draftlol.dawe.gg",
    red: "https://draftlol.dawe.gg", 
    spectator: "https://draftlol.dawe.gg",
    lobby: "https://draftlol.dawe.gg"
  };

  try {
    console.log("🔄 Starting 4fun draft lobby creation...");
    draftLinks = await createDraftLolLobby();
    draftSuccess = true;
    console.log(`✅ 4fun Draft links generated successfully`);
  } catch (err) {
    console.error("❌ Critical error creating 4fun draft lobby:", err);
    draftSuccess = false;
  }

  const components = [];

  if (draftSuccess) {
    const team1Sorted = [...bestTeam1].sort((a,b) => playerData[b].fun.hiddenMMR - playerData[a].fun.hiddenMMR);
    const team2Sorted = [...bestTeam2].sort((a,b) => playerData[b].fun.hiddenMMR - playerData[a].fun.hiddenMMR);

    // Store drafters in match data
    matchData.drafters = {
      blue: team1Sorted[0],
      red: team2Sorted[0]
    };

    const blueDraftButton = new ButtonBuilder()
      .setCustomId('blue_draft_4fun')
      .setLabel('🟦 Blue Team Draft')
      .setStyle(ButtonStyle.Primary);

    const redDraftButton = new ButtonBuilder()
      .setCustomId('red_draft_4fun')
      .setLabel('🔴 Red Team Draft')
      .setStyle(ButtonStyle.Danger);

    const spectatorButton = new ButtonBuilder()
      .setCustomId('spectator_draft_4fun')
      .setLabel('👁️ Spectator View')
      .setStyle(ButtonStyle.Secondary);

    const teamRow = new ActionRowBuilder().addComponents(
      blueDraftButton,
      redDraftButton,
      spectatorButton
    );

    components.push(teamRow);
  }

  const managementRow = new ActionRowBuilder().addComponents(
    new ButtonBuilder()
      .setCustomId(`report_4fun_win_1`)
      .setLabel('🏆 Team 1 Won')
      .setStyle(ButtonStyle.Success),
    new ButtonBuilder()
      .setCustomId(`report_4fun_win_2`)
      .setLabel('🏆 Team 2 Won')
      .setStyle(ButtonStyle.Success)
  );

  components.push(managementRow);

  let embedDescription = `**4Fun Match**\n\n` +
    `**Team OP.GG Links:**\n` +
    `[🔵 Blue Team Multi OP.GG](${team1Link})\n` +
    `[🔴 Red Team Multi OP.GG](${team2Link})\n\n` +
    `**After match, vote with Team Won buttons - 6/10 votes needed**`;

  // Update embed description if draft was successful
  if (draftSuccess) {
    const team1Sorted = [...bestTeam1].sort((a,b) => playerData[b].fun.hiddenMMR - playerData[a].fun.hiddenMMR);
    const team2Sorted = [...bestTeam2].sort((a,b) => playerData[b].fun.hiddenMMR - playerData[a].fun.hiddenMMR);
    
    embedDescription = `**4Fun Match**\n\n` +
      `**Assigned Drafters:**\n` +
      `🔵 Blue Team: <@${team1Sorted[0]}> (Highest MMR)\n` +
      `🔴 Red Team: <@${team2Sorted[0]}> (Highest MMR)\n\n` +
      `**Team OP.GG Links:**\n` +
      `[🔵 Blue Team Multi OP.GG](${team1Link})\n` +
      `[🔴 Red Team Multi OP.GG](${team2Link})\n\n` +
      `**Draft Access:**\n` +
      `• Team draft links: Assigned drafters + Staff only\n` +
      `• Spectator link: Anyone in server\n\n` +
      `**After match, vote with Team Won buttons - 6/10 votes needed**`;
  }

  const matchEmbed = new EmbedBuilder()
    .setTitle("🎉 4Fun Match Lobby")
    .setDescription(embedDescription)
    .addFields(
      {
        name: `🔵 Team 1 (Avg MMR: ${Math.round(bestAvg1)})`,
        value: formatTeamDisplay(bestTeam1),
        inline: false,
      },
      {
        name: `🔴 Team 2 (Avg MMR: ${Math.round(bestAvg2)})`,
        value: formatTeamDisplay(bestTeam2),
        inline: false,
      }
    )
    .setColor(0xff00ff);

  const messageOptions = {
    embeds: [matchEmbed],
    components: components
  };

  if (!draftSuccess) {
    messageOptions.content = `❌ Failed to create draft lobby. Players will need to make draft at https://draftlol.dawe.gg/ manually.`;
  }

  const matchData = {
    team1: bestTeam1,
    team2: bestTeam2,
    matchChannel,
    matchCategory,
    team1VC,
    team2VC,
    matchId: matchId,
    matchMessageId: null,
    votes: {
      team1: new Set(),
      team2: new Set()
    }
  };

  const matchMessage = await matchChannel.send(messageOptions);
  matchData.matchMessageId = matchMessage.id;

  matches4fun.set(matchChannel.id, matchData);

  queue4fun = [];
  startVoteMessageFloodMonitoring(matchChannel, matchData, false);
  saveData();
  update4funQueueMessage();
}

// ---------------- END MATCH ----------------
// ---------------- END MATCH ----------------
async function endMatch(channel, winner, isVoided = false) {
  // Clean up vote timers
  cleanupVoteTimers(channel.id);
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

  // Calculate team average Elo
  const winnersAvgElo = winners.reduce((sum, id) => sum + getIHP(ensurePlayer(id)), 0) / winners.length;
  const losersAvgElo = losers.reduce((sum, id) => sum + getIHP(ensurePlayer(id)), 0) / losers.length;
  
  // Calculate Elo difference adjustment (balanced system)
  const eloDifference = winnersAvgElo - losersAvgElo;
  const eloAdjustment = Math.floor(Math.abs(eloDifference) / 25);

  // Track ELO changes and rank changes
  const eloChanges = [];
  const rankChanges = [];

  // Function to calculate streak bonus/penalty (INFINITE - NO CAP)
  function calculateStreakAdjustment(player, isWinner) {
    const baseLP = 20;
    let streakAdjustment = 0;
    
    if (isWinner) {
      // Win streak logic - INFINITE
      if (player.streakType === "win") {
        streakAdjustment = player.currentStreak; // +1 for 2nd win, +2 for 3rd win, +3 for 4th win, etc.
      } else if (player.streakType === "loss") {
        // Breaking a loss streak - no adjustment
        streakAdjustment = 0;
      } else {
        // First win - no adjustment
        streakAdjustment = 0;
      }
      
      return {
        baseLP: baseLP,
        streakAdjustment: streakAdjustment,
        totalLP: baseLP + streakAdjustment
      };
      
    } else {
      // Loss streak logic - INFINITE  
      if (player.streakType === "loss") {
        streakAdjustment = Math.abs(player.currentStreak); // +1 for 2nd loss, +2 for 3rd loss, +3 for 4th loss, etc.
      } else if (player.streakType === "win") {
        // Breaking a win streak - no adjustment
        streakAdjustment = 0;
      } else {
        // First loss - no adjustment
        streakAdjustment = 0;
      }
      
      // For losses: baseLP + streakAdjustment, but make it negative
      const totalLoss = baseLP + streakAdjustment;
      
      return {
        baseLP: baseLP,
        streakAdjustment: streakAdjustment,
        totalLP: -totalLoss // Always negative for losses
      };
    }
  }

  // Update winners and track changes
  winners.forEach((id) => {
    const p = ensurePlayer(id);
    const oldIHP = getIHP(p);
    const oldRank = p.rank;
    const oldDivision = p.division;
    const oldLP = p.lp;

    // Calculate streak adjustment
    const lpCalculation = calculateStreakAdjustment(p, true);
    
    // === MODIFIED ELO DIFFERENCE ADJUSTMENT FOR WINNERS ===
    // If winners have higher Elo, they get less LP (negative adjustment)
    // If winners have lower Elo, they get more LP (positive adjustment)
    let eloDiffLP;
    if (eloDifference > 0) {
      // Winners are higher rated - they gain 1 less LP per 25 Elo difference
      eloDiffLP = -eloAdjustment;
    } else {
      // Winners are lower rated - they gain 1 more LP per 25 Elo difference  
      eloDiffLP = eloAdjustment;
    }
    
    // Update streak
    if (p.streakType === "win") {
      p.currentStreak += 1;
    } else {
      p.currentStreak = 1;
      p.streakType = "win";
    }

    p.wins++;
    p.lp += lpCalculation.totalLP + eloDiffLP;

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
      newLP: p.lp,
      streakBonus: lpCalculation.streakAdjustment,
      baseLP: lpCalculation.baseLP,
      totalLP: lpCalculation.totalLP + eloDiffLP,
      eloAdjustment: eloDiffLP
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

    // Calculate streak adjustment
    const lpCalculation = calculateStreakAdjustment(p, false);
    
    // === MODIFIED ELO DIFFERENCE ADJUSTMENT FOR LOSERS ===
    // If losers have higher Elo, they lose less LP (positive adjustment - since base is negative)
    // If losers have lower Elo, they lose more LP (negative adjustment - making the loss worse)
    let eloDiffLP;
    if (eloDifference > 0) {
      // Losers are lower rated - they lose 1 more LP per 25 Elo difference
      eloDiffLP = -eloAdjustment;
    } else {
      // Losers are higher rated - they lose 1 less LP per 25 Elo difference
      eloDiffLP = eloAdjustment;
    }
    
    // Update streak
    if (p.streakType === "loss") {
      p.currentStreak -= 1; // Goes more negative
    } else {
      p.currentStreak = -1;
      p.streakType = "loss";
    }

    p.losses++;
    p.lp += lpCalculation.totalLP + eloDiffLP; // This includes both streak adjustment and Elo difference adjustment

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
      newLP: p.lp,
      streakPenalty: lpCalculation.streakAdjustment,
      baseLP: lpCalculation.baseLP,
      totalLP: lpCalculation.totalLP + eloDiffLP,
      eloAdjustment: eloDiffLP
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
      isWinner: change.isWinner,
      streakBonus: change.streakBonus,
      streakPenalty: change.streakPenalty,
      baseLP: change.baseLP,
      totalLP: change.totalLP,
      eloAdjustment: change.eloAdjustment
    })),
    teamElo: {
      winnersAvgElo: Math.round(winnersAvgElo),
      losersAvgElo: Math.round(losersAvgElo),
      eloDifference: Math.round(eloDifference),
      eloAdjustment: eloAdjustment
    },
    voided: isVoided
  };
  
  matchHistory.push(matchRecord);
  await saveMatchHistory(matchHistory);

  saveData();

  // Calculate team average Elo for display
  const team1AvgElo = Math.round(team1.reduce((sum, id) => sum + getIHP(ensurePlayer(id)), 0) / team1.length);
  const team2AvgElo = Math.round(team2.reduce((sum, id) => sum + getIHP(ensurePlayer(id)), 0) / team2.length);

  // Create enhanced history embed with ELO changes and streak info
  const team1Players = team1.map(id => `<@${id}>`).join(", ") || "—";
  const team2Players = team2.map(id => `<@${id}>`).join(", ") || "—";

  // Build ELO changes display WITHOUT streak information
  const eloChangesText = eloChanges.map(change => {
    const changeSymbol = change.change >= 0 ? "🟢" : "🔴";
    const changeText = change.change >= 0 ? `+${change.change}` : `${change.change}`;
    const winLoss = change.isWinner ? "🏆" : "💀";
    
    const oldRankDisplay = change.oldDivision ? `${change.oldRank} ${change.oldDivision}` : change.oldRank;
    const newRankDisplay = change.newDivision ? `${change.newRank} ${change.newDivision}` : change.newRank;
    
    return `${winLoss} <@${change.id}>: ${oldRankDisplay} ${change.oldLP}LP → ${newRankDisplay} ${change.newLP}LP (${changeSymbol} ${changeText} ELO)`;
  }).join('\n');

  // Calculate team average Elo for display - USE PRE-MATCH ELO
  const team1PreMatchAvg = Math.round(team1.reduce((sum, id) => {
    const playerChange = eloChanges.find(change => change.id === id);
    return sum + (playerChange ? playerChange.oldIHP : getIHP(ensurePlayer(id)));
  }, 0) / team1.length);

  const team2PreMatchAvg = Math.round(team2.reduce((sum, id) => {
    const playerChange = eloChanges.find(change => change.id === id);
    return sum + (playerChange ? playerChange.oldIHP : getIHP(ensurePlayer(id)));
  }, 0) / team2.length);

  // Elo difference information
  const eloDifferenceInfo = `**Elo Difference:** ${Math.round(eloDifference)}`;

  // ADD MATCH ID TO THE EMBED TITLE AND DESCRIPTION
  const embed = new EmbedBuilder()
    .setTitle(`📜 Match History - ID: ${matchId}`)
    .setDescription(`**Match ID:** ${matchId}\n**Winner:** ${winner === "1" ? "🟦 Team 1 (Blue)" : "🟥 Team 2 (Red)"}\n${eloDifferenceInfo}`)
    .addFields(
      { name: `🟦 Team 1 (Blue) - Avg Elo: ${team1PreMatchAvg}`, value: team1Players, inline: false },
      { name: `🟥 Team 2 (Red) - Avg Elo: ${team2PreMatchAvg}`, value: team2Players, inline: false },
      { name: "📈 ELO Changes", value: eloChangesText || "No changes", inline: false }
    )
    .setColor(winner === "1" ? 0x3498db : 0xe74c3c)
    .setTimestamp()
    .setFooter({ text: `Match ID: ${matchId} | Use !changewinner or !voidmatch with this ID` });

  // Send main history embed
  await historyChannel.send({ embeds: [embed] });

  // Send streak notifications
  const streakNotifications = [];
  
  winners.forEach(id => {
    const player = ensurePlayer(id);
    if (player.currentStreak >= 2) {
      streakNotifications.push(`🔥 <@${id}> is on a ${player.currentStreak} game win streak!`);
    }
  });
  
  losers.forEach(id => {
    const player = ensurePlayer(id);
    if (player.currentStreak <= -2) {
      streakNotifications.push(`😔 <@${id}> is on a ${Math.abs(player.currentStreak)} game loss streak.`);
    }
  });
  
  if (streakNotifications.length > 0) {
    const streakEmbed = new EmbedBuilder()
      .setTitle("📊 Streak Updates")
      .setDescription(streakNotifications.join('\n'))
      .setColor(0xffa500)
      .setTimestamp();
    
    await historyChannel.send({ embeds: [streakEmbed] });
  }

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

async function end4funMatch(channel, winner) {
  // Clean up vote timers
  cleanupVoteTimers(channel.id);
  const match = matches4fun.get(channel.id);
  if (!match) {
    return channel.send("❌ No active 4fun match found in this channel.");
  }

  const { team1, team2, matchChannel, matchCategory, team1VC, team2VC, matchId } = match;
  const guild = channel.guild;

  const winners = winner === "1" ? team1 : team2;
  const losers = winner === "1" ? team2 : team1;

  // Calculate team average MMR for Elo calculation
  const winnersAvgMMR = winners.reduce((sum, id) => sum + ensurePlayer(id).fun.hiddenMMR, 0) / winners.length;
  const losersAvgMMR = losers.reduce((sum, id) => sum + ensurePlayer(id).fun.hiddenMMR, 0) / losers.length;

  // Update hidden MMR using same Elo system as main game
  winners.forEach((id) => {
    const p = ensurePlayer(id);
    const oldMMR = p.fun.hiddenMMR;
    
    // Elo calculation
    const expected = 1 / (1 + 10 ** ((losersAvgMMR - oldMMR) / 400));
    const newMMR = oldMMR + 32 * (1 - expected);
    
    p.fun.hiddenMMR = newMMR;
    p.fun.points = Math.max(0, p.fun.points + FUN_POINTS_PER_GAME); // Can't go below 0
    p.fun.wins++;
    p.fun.matchesPlayed++;
  });

  losers.forEach((id) => {
    const p = ensurePlayer(id);
    const oldMMR = p.fun.hiddenMMR;
    
    // Elo calculation
    const expected = 1 / (1 + 10 ** ((winnersAvgMMR - oldMMR) / 400));
    const newMMR = oldMMR + 32 * (0 - expected);
    
    p.fun.hiddenMMR = newMMR;
    p.fun.points = Math.max(0, p.fun.points - FUN_POINTS_PER_GAME); // Can't go below 0
    p.fun.losses++;
    p.fun.matchesPlayed++;
  });

  saveData();

  // Send confirmation message
  await channel.send(`✅ 4Fun Match ${matchId} ended! ${winner === "1" ? "🟦 Team 1 (Blue)" : "🔴 Team 2 (Red)"} wins!`);

  // Delete match channels
  try {
    if (team1VC) await team1VC.delete().catch(console.error);
    if (team2VC) await team2VC.delete().catch(console.error);
    if (matchChannel) await matchChannel.delete().catch(console.error);
    if (matchCategory) await matchCategory.delete().catch(console.error);
  } catch (err) {
    console.error("Error deleting 4fun match channels:", err);
  }

  // Remove from active matches
  matches4fun.delete(channel.id);
  
  // Update 4fun leaderboard
  await update4funLeaderboardChannel(guild);
}

// ---------------- READY ----------------
const MAIN_GUILD_ID = "1423242905602101310";

client.once("ready", async () => {
  console.log(`✅ Logged in as ${client.user.tag}`);
  
  // Connect to MongoDB first
  await connectDB();
  
  // Load data from MongoDB/file
  playerData = await loadData();

  // Initialize match ID counter
  await initializeMatchIdCounter();
  
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

  // Queue setup - with improved existing message detection
  let queueChannel = guild.channels.cache.find((c) => c.name === "queue");
  if (!queueChannel) {
    queueChannel = await guild.channels.create({ name: "queue", type: 0 });
    console.log("Created new queue channel");
  }

  // 4fun queue setup - with improved existing message detection
  let queue4funChannel = guild.channels.cache.find((c) => c.name === "4fun-queue");
  if (!queue4funChannel) {
    queue4funChannel = await guild.channels.create({ name: "4fun-queue", type: 0 });
    console.log("Created new 4fun-queue channel");
  }

  // These functions will now reuse existing messages if found
  await post4funQueueMessage(queue4funChannel);
  await postQueueMessage(queueChannel);

  // 4fun leaderboard setup
  await update4funLeaderboardChannel(guild);
  
  console.log('✅ Bot fully initialized with data loaded');
  console.log('✅ Bot fully initialized with 4fun system');
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