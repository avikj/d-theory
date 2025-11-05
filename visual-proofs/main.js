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
renderer.setSize(window.innerWidth, window.innerHeight);
renderer.domElement.style.position = 'absolute';
renderer.domElement.style.top = '0px';
renderer.domElement.style.left = '0px';
document.getElementById('scene-container').appendChild(renderer.domElement);

const labelRenderer = new CSS2DRenderer();
labelRenderer.setSize(window.innerWidth, window.innerHeight);
labelRenderer.domElement.style.position = 'absolute';
labelRenderer.domElement.style.top = '0px';
labelRenderer.domElement.style.left = '0px';
labelRenderer.domElement.style.pointerEvents = 'none'; // Allow mouse events to pass through
document.getElementById('scene-container').appendChild(labelRenderer.domElement);

// 3. Create and position concept nodes
const nodes = {};
const concepts = Object.keys(conceptualGraph);
const radius = 10;

concepts.forEach((conceptName, index) => {
    const angle = (index / concepts.length) * 2 * Math.PI;
    const x = radius * Math.cos(angle);
    const z = radius * Math.sin(angle);

    const geometry = new THREE.SphereGeometry(1, 32, 32);
    const material = new THREE.MeshBasicMaterial({ color: Math.random() * 0xffffff });
    const sphere = new THREE.Mesh(geometry, material);

    sphere.position.set(x, 0, z);
    nodes[conceptName] = sphere;
    scene.add(sphere);

    // Create label
    const labelDiv = document.createElement('div');
    labelDiv.className = 'concept-label';
    labelDiv.textContent = conceptName;
    labelDiv.style.marginTop = '-1em'; // Adjust position

    const conceptLabel = new CSS2DObject(labelDiv);
    conceptLabel.position.set(x, 1.5, z); // Position above the sphere
    scene.add(conceptLabel);
});

camera.position.z = 20;

// 4. Draw connections
const lineMaterial = new THREE.LineBasicMaterial({ color: 0xffffff, transparent: true, opacity: 0.5 });

concepts.forEach(conceptName => {
    const sourceNode = nodes[conceptName];
    const connections = conceptualGraph[conceptName].connections;

    connections.forEach(targetName => {
        const targetNode = nodes[targetName];
        if (targetNode) {
            const geometry = new THREE.BufferGeometry().setFromPoints([sourceNode.position, targetNode.position]);
            const line = new THREE.Line(geometry, lineMaterial);
            scene.add(line);
        }
    });
});

// 4. Animation Loop
function animate() {
    requestAnimationFrame(animate);

    // Animate the nodes (e.g., make them float)
    Object.values(nodes).forEach(node => {
        node.position.y = Math.sin(Date.now() * 0.001 + node.position.x) * 0.5;
    });

    renderer.render(scene, camera);
    labelRenderer.render(scene, camera);
}

animate();

// 5. Handle window resize
window.addEventListener('resize', () => {
    camera.aspect = window.innerWidth / window.innerHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(window.innerWidth, window.innerHeight);
    labelRenderer.setSize(window.innerWidth, window.innerHeight);
});
