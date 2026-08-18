import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

export default defineConfig({
  plugins: [react()],
  // relative base so the build works at github.io/<repo>/ without hardcoding the repo name
  base: "./",
});
