# Padayon Live Backend (Render)

This backend enables:

- ✅ Online users (presence)
- ✅ Admin sees what users are doing (activity + path)
- ✅ Live library sync (admin edits instantly show on clients)
- ✅ Admin can create accounts inside Admin Panel

## Run locally

```bash
cd backend
npm install
npm start
```

Server runs at: http://localhost:3000

## Environment variables

- `JWT_SECRET` **(required in production)**: random secret for login tokens
- `CORS_ORIGIN`: comma-separated allowed frontend origins (or `*`)
- `DATA_DIR`: folder where `db.json` is stored (use Render Disk mount path)

Example:

```bash
JWT_SECRET="change-me" CORS_ORIGIN="http://localhost:5500" npm start
```

## Important notes

- If you don't use a persistent disk/database, created accounts + admin library edits will be lost on redeploy/restart.
- Render Free web services can spin down after inactivity, which will disconnect WebSockets.
