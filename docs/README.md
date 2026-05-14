# Interactive Companion

Browser-based companion app for **"Timing, Entry, and Revenue in
Clock-Based Platform Markets"** (Pitz & Ferraz, 2026).

The app implements the mechanism comparison from the paper (Dutch
auction vs. fixed-price immediate vs. fixed-price batch) as an
interactive React widget. Sliders control the primitives (clock speed,
outside option, ratio θ, etc.); the panels render attractiveness,
entry, prices, and revenue in real time.

All formulas mirror `code/lib.py`. See `model.js` for the JavaScript
port.

Built as a single static page; no build step, no server. Open
`index.html` locally or visit the deployed version at
https://vferraz.github.io/dutch-auctions-matching-markets/
