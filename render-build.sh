#!/bin/bash
echo "🚀 Starting Render build process for Puppeteer..."

# Install Chrome dependencies
apt-get update
apt-get install -y wget gnupg

# Download and install Chrome
wget -q -O - https://dl-ssl.google.com/linux/linux_signing_key.pub | apt-key add -
echo "deb [arch=amd64] http://dl.google.com/linux/chrome/deb/ stable main" >> /etc/apt/sources.list.d/google.list
apt-get update
apt-get install -y google-chrome-stable

# Verify installation
echo "✅ Chrome installed at: $(which google-chrome)"