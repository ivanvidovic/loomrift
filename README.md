# PD_LoomRift

Procedural gradient-tile collage generator. Exports SVG (editable in Illustrator) and PNG.

## Run locally

```bash
npm install
npm run dev
```

## Deploy to GitHub Pages

1. Push this repo to GitHub with `main` as the default branch.
2. Repo **Settings → Pages → Build and deployment → Source: GitHub Actions**.
3. Push. The workflow in `.github/workflows/deploy.yml` builds and publishes to
   `https://<user>.github.io/<repo>/`.

`vite.config.js` uses `base: "./"`, so the build works under any repo name
without editing config.

## Notes

- Saved looks are stored in `localStorage`, per browser.
- Illustrator strips `mix-blend-mode` on SVG import. Layer groups keep their
  names, so blend modes can be reapplied per group after placing.
- "Expand geometry on export" duplicates tile geometry instead of using `<use>`
  references. Leave it on for Illustrator.
