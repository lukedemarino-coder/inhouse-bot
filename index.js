async function connectDB() {
    try {
        console.log('🔗 Connecting to MongoDB...');
        
        const client = new MongoClient(process.env.MONGODB_URI, {
            tls: true,
            tlsAllowInvalidCertificates: false,
            tlsInsecure: false,
            retryWrites: true,
            w: 'majority',
            serverSelectionTimeoutMS: 5000,
            socketTimeoutMS: 45000,
            maxPoolSize: 10,
            minPoolSize: 1
        });
        
        await client.connect();
        
        // Test the connection
        await client.db().admin().ping();
        
        db = client.db('discord-bot');
        playerDataCollection = db.collection('playerData');
        matchHistoryCollection = db.collection('matchHistory');
        console.log('✅ Connected to MongoDB successfully!');
    } catch (error) {
        console.error('❌ MongoDB connection failed:', error);
        console.log('⚠️  Falling back to local file storage');
    }
}
