// 1. Conceptual Graph Data
const conceptualGraph = {
    "Monochrome": {
        connections: ["MonochromeIridescence"]
    },
    "Iridescence": {
        connections: ["MonochromeIridescence"]
    },
    "MonochromeIridescence": {
        connections: ["Grayscale as Rainbow", "The Pearl", "The Hologram", "The Mathematician", "The Distinction"]
    },
    "Grayscale as Rainbow": {
        connections: []
    },
    "The Pearl": {
        connections: []
    },
    "The Hologram": {
        connections: []
    },
    "The Mathematician": {
        connections: []
    },
    "The Distinction": {
        connections: []
    }
};

// 2. Three.js Scene Setup
const scene = new THREE.Scene();
const camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000);
const renderer = new THREE.WebGLRenderer({ antialias: true });

const container = document.getElementById('scene-container');
renderer.setSize(window.innerWidth, window.innerHeight);
container.appendChild(renderer.domElement);

// 3. Basic Scene Content (a test cube)
const geometry = new THREE.BoxGeometry();
const material = new THREE.MeshBasicMaterial({ color: 0x00ff00 });
const cube = new THREE.Mesh(geometry, material);
scene.add(cube);

camera.position.z = 5;

// 4. Animation Loop
function animate() {
    requestAnimationFrame(animate);

    cube.rotation.x += 0.01;
    cube.rotation.y += 0.01;

    renderer.render(scene, camera);
}

animate();

// 5. Handle window resize
window.addEventListener('resize', () => {
    camera.aspect = window.innerWidth / window.innerHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(window.innerWidth, window.innerHeight);
});
