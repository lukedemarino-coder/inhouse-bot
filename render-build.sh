#!/bin/bash
echo "🚀 Starting Render build process for Puppeteer..."

# Update and install dependencies
apt-get update
apt-get install -y wget gnupg unzip

# Install Google Chrome
wget -q -O - https://dl.google.com/linux/linux_signing_key.pub | apt-key add -
echo "deb [arch=amd64] http://dl.google.com/linux/chrome/deb/ stable main" >> /etc/apt/sources.list.d/google-chrome.list
apt-get update
apt-get install -y google-chrome-stable

# Verify Chrome installation
if [ -f "/usr/bin/google-chrome" ]; then
    echo "✅ Chrome successfully installed at: /usr/bin/google-chrome"
    /usr/bin/google-chrome --version
else
    echo "❌ Chrome installation failed - checking alternatives..."
    # Try to find where Chrome was installed
    find / -name "google-chrome" 2>/dev/null || echo "Chrome not found anywhere"
fi

# Also install Chromium as backup
apt-get install -y chromium-browser
if [ -f "/usr/bin/chromium-browser" ]; then
    echo "✅ Chromium installed at: /usr/bin/chromium-browser"
    /usr/bin/chromium-browser --version
fi