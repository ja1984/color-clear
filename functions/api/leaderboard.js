const KEY = 'leaderboard';
const MAX_ENTRIES = 100;
const TOP_N = 20;

const json = (data, status = 200) =>
  new Response(JSON.stringify(data), {
    status,
    headers: { 'content-type': 'application/json' },
  });

async function readBoard(kv) {
  const raw = await kv.get(KEY);
  if (!raw) return [];
  try {
    const parsed = JSON.parse(raw);
    return Array.isArray(parsed) ? parsed : [];
  } catch {
    return [];
  }
}

export async function onRequestGet({ env }) {
  const board = await readBoard(env.leaderboard);
  return json(board.slice(0, TOP_N));
}

export async function onRequestPost({ request, env }) {
  let body;
  try {
    body = await request.json();
  } catch {
    return json({ error: 'invalid json' }, 400);
  }

  const name = String(body?.name ?? '').trim().slice(0, 20) || 'Anon';
  const score = Math.max(0, Math.floor(Number(body?.score) || 0));
  const level = Math.max(1, Math.floor(Number(body?.level) || 1));

  const entry = { name, score, level, at: Date.now() };
  const board = await readBoard(env.leaderboard);
  board.push(entry);
  board.sort((a, b) => b.score - a.score || a.at - b.at);
  const trimmed = board.slice(0, MAX_ENTRIES);
  await env.leaderboard.put(KEY, JSON.stringify(trimmed));

  return json({ ok: true, top: trimmed.slice(0, TOP_N) });
}
