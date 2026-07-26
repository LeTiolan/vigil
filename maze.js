// ================================================================
//  MAZE GENERATION + PATHFINDING
// ================================================================
export const MAZE_SIZE = 33, TILE_SIZE = 9;

export const maze = Array(MAZE_SIZE).fill(null).map(() => Array(MAZE_SIZE).fill(1));
export const emptyCells = [];

function carveMaze(x, y) {
    maze[x][y] = 0;
    const dirs = [[0, -1], [0, 1], [-1, 0], [1, 0]].sort(() => Math.random() - 0.5);
    for (const [dx, dy] of dirs) {
        const nx = x + dx * 2, ny = y + dy * 2;
        if (nx > 0 && nx < MAZE_SIZE - 1 && ny > 0 && ny < MAZE_SIZE - 1 && maze[nx][ny] === 1) {
            maze[x + dx][y + dy] = 0;
            carveMaze(nx, ny);
        }
    }
}
carveMaze(1, 1);

// Carve a few open rooms (breathing room + landmarks) away from spawn/exit
export const rooms = [];
{
    const tries = 40, half = 2; // 5x5 rooms
    for (let t = 0; t < tries && rooms.length < 3; t++) {
        const cx = 4 + Math.floor(Math.random() * (MAZE_SIZE - 8));
        const cz = 4 + Math.floor(Math.random() * (MAZE_SIZE - 8));
        if (Math.hypot(cx - 1, cz - 1) < 8 || Math.hypot(cx - Math.floor(MAZE_SIZE / 2), cz - (MAZE_SIZE - 1)) < 8) continue;
        if (rooms.some(r => Math.hypot(r.x - cx, r.z - cz) < 8)) continue;
        for (let i = cx - half; i <= cx + half; i++) for (let j = cz - half; j <= cz + half; j++)
            if (i > 0 && i < MAZE_SIZE - 1 && j > 0 && j < MAZE_SIZE - 1) maze[i][j] = 0;
        rooms.push({ x: cx, z: cz });
    }
}

for (let i = 1; i < MAZE_SIZE - 1; i++) for (let j = 1; j < MAZE_SIZE - 1; j++)
    if (maze[i][j] === 1 && ((maze[i - 1][j] === 0 && maze[i + 1][j] === 0) || (maze[i][j - 1] === 0 && maze[i][j + 1] === 0)) && Math.random() < 0.25) maze[i][j] = 0;

export const exitGridX = Math.floor(MAZE_SIZE / 2), exitGridZ = MAZE_SIZE - 1;
for (let i = -1; i <= 1; i++) for (let j = -3; j <= -1; j++) maze[exitGridX + i][exitGridZ + j] = 0;
maze[exitGridX][exitGridZ] = 0;

for (let i = 0; i < MAZE_SIZE; i++) for (let j = 0; j < MAZE_SIZE; j++) if (maze[i][j] === 0) emptyCells.push({ x: i, z: j });

export function getPos(i, j) { return { x: (i - Math.floor(MAZE_SIZE / 2)) * TILE_SIZE, z: (j - Math.floor(MAZE_SIZE / 2)) * TILE_SIZE }; }

export function worldToGrid(wx, wz) {
    const o = Math.floor(MAZE_SIZE / 2);
    return { x: Math.max(0, Math.min(MAZE_SIZE - 1, Math.round(wx / TILE_SIZE) + o)), z: Math.max(0, Math.min(MAZE_SIZE - 1, Math.round(wz / TILE_SIZE) + o)) };
}

export function bfsPath(sx, sz, gx, gz) {
    if (sx === gx && sz === gz) return [];

    // OPTIMIZATION: Flat typed arrays are blisteringly fast and O(1) complexity.
    // This prevents the JS engine from choking or creating circular reference loops.
    const visited = new Uint8Array(MAZE_SIZE * MAZE_SIZE);
    const parent = new Int16Array(MAZE_SIZE * MAZE_SIZE);
    parent.fill(-1);

    const startIdx = sx + sz * MAZE_SIZE;
    const targetIdx = gx + gz * MAZE_SIZE;

    const q = [startIdx];
    visited[startIdx] = 1;

    let head = 0;
    let it = 0;

    // Loop limit protects against unexpected grid lockups
    while (head < q.length && it++ < 3000) {
        const curr = q[head++];
        const cx = curr % MAZE_SIZE;
        const cz = Math.floor(curr / MAZE_SIZE);

        // If we reached the target, trace back safely
        if (curr === targetIdx) {
            const path = [];
            let p = curr;
            let failsafe = 0; // Absolute protection against infinite while-loops

            while (p !== -1 && parent[p] !== -1 && failsafe++ < 1000) {
                path.unshift({ x: p % MAZE_SIZE, z: Math.floor(p / MAZE_SIZE) });
                p = parent[p];
            }
            // Remove the very first node so they don't stutter in place
            if (path.length) path.shift();
            return path;
        }

        // Strictly 4-directional movement to prevent clipping corners and walls
        const neighbors = [];
        if (cz > 0) neighbors.push(curr - MAZE_SIZE); // Up
        if (cz < MAZE_SIZE - 1) neighbors.push(curr + MAZE_SIZE); // Down
        if (cx > 0) neighbors.push(curr - 1); // Left
        if (cx < MAZE_SIZE - 1) neighbors.push(curr + 1); // Right

        for (let i = 0; i < neighbors.length; i++) {
            const n = neighbors[i];
            const nx = n % MAZE_SIZE;
            const nz = Math.floor(n / MAZE_SIZE);

            // Only traverse if it is an empty corridor (0) and hasn't been visited
            if (maze[nx][nz] === 0 && visited[n] === 0) {
                visited[n] = 1;
                parent[n] = curr;
                q.push(n);
            }
        }
    }
    return [];
}

export function hasLOS(ax, az, bx, bz) {
    const g0 = worldToGrid(ax, az), g1 = worldToGrid(bx, bz), steps = Math.max(Math.abs(g1.x - g0.x), Math.abs(g1.z - g0.z));
    if (!steps) return true;
    for (let i = 1; i < steps; i++) {
        const t = i / steps, cx = Math.round(g0.x + (g1.x - g0.x) * t), cz = Math.round(g0.z + (g1.z - g0.z) * t);
        if (cx >= 0 && cx < MAZE_SIZE && cz >= 0 && cz < MAZE_SIZE && maze[cx][cz] === 1) return false;
    }
    return true;
}
