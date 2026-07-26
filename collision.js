import * as THREE from 'three';
import { MAZE_SIZE, TILE_SIZE, maze } from './maze.js';
import { player } from './state.js';

// ================================================================
//  COLLISION
//
//  isWall() takes `doorGroup` as a parameter (rather than importing
//  it from door.js) specifically to avoid a circular import: door.js
//  needs registerSolid() from this file while it's being built, and
//  that happens before door.js would be able to hand back doorGroup.
// ================================================================
export const solidDoorParts = [], partBox = new THREE.Box3();
// Static parts (pillars, lintel, terminal housing) get their AABB computed
// once and cached. Parts that move (the sliding door panels) are flagged
// live:true by door.js and get recomputed every check.
const cachedBoxes = new Map();
export function registerSolid(m, live) {
    solidDoorParts.push(m);
    if (!live) cachedBoxes.set(m, new THREE.Box3().setFromObject(m));
}

// World props (fallen wall debris, crates) can be anywhere on the map and
// are always static, so — unlike door parts — they're checked everywhere,
// not gated by proximity to one location. List stays short (tens of
// entries), so an unconditional scan every isWall() call is cheap.
const worldSolids = [];
export function registerPropSolid(m) {
    worldSolids.push(new THREE.Box3().setFromObject(m));
}

const _pBox = new THREE.Box3(new THREE.Vector3(), new THREE.Vector3());

export function isWall(x, z, r, doorGroup) {
    const off = Math.floor(MAZE_SIZE / 2);
    const x0 = Math.floor((x - r + TILE_SIZE / 2) / TILE_SIZE) + off - 1, x1 = Math.floor((x + r + TILE_SIZE / 2) / TILE_SIZE) + off + 1;
    const z0 = Math.floor((z - r + TILE_SIZE / 2) / TILE_SIZE) + off - 1, z1 = Math.floor((z + r + TILE_SIZE / 2) / TILE_SIZE) + off + 1;
    for (let i = x0; i <= x1; i++) for (let j = z0; j <= z1; j++) {
        if (i < 0 || i >= MAZE_SIZE || j < 0 || j >= MAZE_SIZE || maze[i][j] !== 1) continue;
        const wx = (i - off) * TILE_SIZE, wz = (j - off) * TILE_SIZE;
        const cx = Math.max(wx - TILE_SIZE / 2, Math.min(x, wx + TILE_SIZE / 2)), cz = Math.max(wz - TILE_SIZE / 2, Math.min(z, wz + TILE_SIZE / 2));
        if ((x - cx) * (x - cx) + (z - cz) * (z - cz) < r * r) return true;
    }

    const nearDoor = doorGroup && Math.abs(x - doorGroup.position.x) < TILE_SIZE && Math.abs(z - doorGroup.position.z) < TILE_SIZE;
    if (nearDoor || worldSolids.length) {
        _pBox.min.set(x - r, 0, z - r); _pBox.max.set(x + r, player.height, z + r);
        if (nearDoor) {
            for (const sp of solidDoorParts) {
                const cached = cachedBoxes.get(sp);
                if (cached) { if (_pBox.intersectsBox(cached)) return true; }
                else { partBox.setFromObject(sp); if (_pBox.intersectsBox(partBox)) return true; }
            }
        }
        for (const box of worldSolids) { if (_pBox.intersectsBox(box)) return true; }
    }
    return false;
}
