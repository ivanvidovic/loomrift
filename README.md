# Visual Loom

Procedural gradient-tile pattern generator. Exports vector SVG and PNG.

## Run locally

```bash
npm install
npm run dev
```

## Deploy to GitHub Pages

1. Push to GitHub with `main` as the default branch.
2. Repo **Settings → Pages → Build and deployment → Source: GitHub Actions**.
3. Push. The workflow in `.github/workflows/deploy.yml` builds and publishes to
   `https://<user>.github.io/<repo>/`.

`vite.config.js` uses `base: "./"`, so the build works under any repo name
without editing config.

## Notes

- Saved looks are stored in `localStorage`, per browser.
- The preview renders to canvas for speed; exports are true vector.
- "Expand geometry on export" duplicates tile geometry instead of using `<use>`
  references, producing a simpler file to edit downstream.
