// Application state
let pods = [];
let selectedPodId = null;
let podDetailsCache = {}; // Cache for POD details

// LocalStorage keys
const PODS_STORAGE_KEY = 'pod2_pods';
const SELECTED_POD_STORAGE_KEY = 'pod2_selected_pod';
const POD_DETAILS_CACHE_KEY = 'pod2_pod_details_cache';

// DOM elements
const refreshBtn = document.getElementById('refresh-pods-btn');
const loadLocalPodsBtn = document.getElementById('load-local-pods-btn');
const clearStorageBtn = document.getElementById('clear-storage-btn');
const podList = document.getElementById('pod-list');
const podDetails = document.getElementById('pod-details');
const tabButtons = document.querySelectorAll('.tab-btn');
const tabContents = document.querySelectorAll('.tab-content');
const createPodForm = document.getElementById('create-pod-form');
const addEntryBtn = document.getElementById('add-entry-btn');
const entriesContainer = document.getElementById('entries-container');
const visualizeAllPodsBtn = document.getElementById('visualize-all-pods-btn');
const visualizationType = document.getElementById('visualization-type');
const visualizationContainer = document.getElementById('visualization-container');

// API endpoints
const API_BASE_URL = '/api';
const API_PODS = `${API_BASE_URL}/pods`;

// Functions for local storage
function savePods() {
    try {
        if (Array.isArray(pods) && pods.length > 0) {
            localStorage.setItem(PODS_STORAGE_KEY, JSON.stringify(pods));
            console.log('Saved pods to localStorage:', pods);
        } else {
            console.warn('Not saving pods to localStorage because the array is empty');
        }
    } catch (error) {
        console.error('Error saving pods to localStorage:', error);
    }
}

function saveSelectedPod() {
    try {
        localStorage.setItem(SELECTED_POD_STORAGE_KEY, selectedPodId);
    } catch (error) {
        console.error('Error saving selected pod to localStorage:', error);
    }
}

function loadPodsFromStorage() {
    try {
        const storedPods = localStorage.getItem(PODS_STORAGE_KEY);
        if (storedPods) {
            const parsedPods = JSON.parse(storedPods);
            // Make sure we have a valid array of pods
            if (Array.isArray(parsedPods) && parsedPods.length > 0) {
                pods = parsedPods;
                console.log('Loaded pods from localStorage:', pods);
                return true;
            }
        }
    } catch (error) {
        console.error('Error loading pods from localStorage:', error);
    }
    return false;
}

function loadSelectedPodFromStorage() {
    try {
        const storedSelectedPod = localStorage.getItem(SELECTED_POD_STORAGE_KEY);
        if (storedSelectedPod) {
            selectedPodId = storedSelectedPod;
            return true;
        }
    } catch (error) {
        console.error('Error loading selected pod from localStorage:', error);
    }
    return false;
}

function savePodDetailsCache() {
    try {
        if (typeof podDetailsCache === 'object' && podDetailsCache !== null && Object.keys(podDetailsCache).length > 0) {
            localStorage.setItem(POD_DETAILS_CACHE_KEY, JSON.stringify(podDetailsCache));
            console.log('Saved pod details cache to localStorage:', Object.keys(podDetailsCache));
        } else {
            console.warn('Not saving pod details cache to localStorage because it is empty');
        }
    } catch (error) {
        console.error('Error saving pod details cache to localStorage:', error);
    }
}

function loadPodDetailsCacheFromStorage() {
    try {
        const storedCache = localStorage.getItem(POD_DETAILS_CACHE_KEY);
        if (storedCache) {
            const parsedCache = JSON.parse(storedCache);
            // Make sure we have a valid object with at least one key
            if (typeof parsedCache === 'object' && parsedCache !== null && Object.keys(parsedCache).length > 0) {
                podDetailsCache = parsedCache;
                console.log('Loaded pod details cache from localStorage:', Object.keys(podDetailsCache));
                return true;
            }
        }
    } catch (error) {
        console.error('Error loading pod details cache from localStorage:', error);
    }
    return false;
}

// Event listeners
document.addEventListener('DOMContentLoaded', () => {
    console.log('DOM loaded, checking localStorage');
    
    // Try to load pods from local storage first
    const podsLoaded = loadPodsFromStorage();
    const cacheLoaded = loadPodDetailsCacheFromStorage();
    const selectedPodLoaded = loadSelectedPodFromStorage();
    
    console.log('Storage check results:', {
        podsLoaded,
        cacheLoaded,
        selectedPodLoaded,
        selectedPodId,
        hasPodDetailsForSelected: selectedPodId && podDetailsCache[selectedPodId]
    });
    
    if (podsLoaded) {
        renderPodList();
        
        // If we have a selected pod with details, render it
        if (selectedPodId && cacheLoaded && podDetailsCache[selectedPodId]) {
            console.log('Rendering cached pod details for:', selectedPodId);
            renderPodDetails(podDetailsCache[selectedPodId]);
        } else if (selectedPodId) {
            console.log('Fetching pod details from server for:', selectedPodId);
            loadPodDetails(selectedPodId);
        }
    } else {
        // If no pods in local storage, fetch from server
        console.log('No pods in localStorage, fetching from server');
        loadPods();
    }
    
    // Tab switching
    tabButtons.forEach(button => {
        button.addEventListener('click', () => {
            // Deactivate all tabs
            tabButtons.forEach(btn => btn.classList.remove('active'));
            tabContents.forEach(content => content.classList.remove('active'));
            
            // Activate selected tab
            button.classList.add('active');
            const tabId = button.getAttribute('data-tab');
            document.getElementById(tabId).classList.add('active');
        });
    });
    
    // Refresh pods button (from server)
    refreshBtn.addEventListener('click', () => {
        // Clear the cache when refreshing from server
        podDetailsCache = {};
        localStorage.removeItem(POD_DETAILS_CACHE_KEY);
        
        // Load pods from server
        loadPods();
    });
    
    // Load from local storage button
    loadLocalPodsBtn.addEventListener('click', () => {
        if (loadPodsFromStorage() && loadPodDetailsCacheFromStorage()) {
            renderPodList();
            
            // If there's a selected pod, load its details
            if (loadSelectedPodFromStorage() && selectedPodId && podDetailsCache[selectedPodId]) {
                renderPodDetails(podDetailsCache[selectedPodId]);
            }
            
            showStatusMessage('Loaded PODs from local storage', 'success');
        } else {
            showStatusMessage('No PODs found in local storage', 'error');
        }
    });
    
    // Clear storage button
    clearStorageBtn.addEventListener('click', () => {
        if (confirm('Are you sure you want to clear all local storage data?')) {
            localStorage.removeItem(PODS_STORAGE_KEY);
            localStorage.removeItem(SELECTED_POD_STORAGE_KEY);
            localStorage.removeItem(POD_DETAILS_CACHE_KEY);
            
            // Reset application state
            pods = [];
            selectedPodId = null;
            podDetailsCache = {};
            
            // Clear UI
            renderPodList();
            podDetails.innerHTML = '<p class="select-message">Select a POD from the sidebar to view details</p>';
            
            showStatusMessage('Local storage cleared successfully', 'success');
        }
    });
    
    // Add entry button
    addEntryBtn.addEventListener('click', addEntryRow);
    
    // Remove entry button delegation
    entriesContainer.addEventListener('click', (e) => {
        if (e.target.classList.contains('remove-entry-btn')) {
            // Don't remove the last entry row
            if (entriesContainer.children.length > 1) {
                e.target.closest('.entry-row').remove();
            }
        }
    });
    
    // Create POD form
    createPodForm.addEventListener('submit', handleCreatePod);
    
    // Visualization button
    visualizeAllPodsBtn.addEventListener('click', handleVisualizePods);
});

// Load PODs from the API
async function loadPods() {
    try {
        const response = await fetch(API_PODS);
        const data = await response.json();
        
        pods = data.pods || [];
        console.log('Loaded pods from API:', pods);
        
        // Save to local storage if not empty
        if (pods.length > 0) {
            savePods();
        } else {
            console.log('No pods loaded from API');
        }
        
        renderPodList();
    } catch (error) {
        console.error('Error loading pods:', error);
        showStatusMessage('Failed to load PODs', 'error');
    }
}

// Render the POD list in the sidebar
function renderPodList() {
    podList.innerHTML = '';
    
    if (pods.length === 0) {
        podList.innerHTML = '<p>No PODs available</p>';
        return;
    }
    
    pods.forEach(pod => {
        const podItem = document.createElement('div');
        podItem.className = 'pod-item';
        
        // Highlight the selected POD
        if (pod.id === selectedPodId) {
            podItem.classList.add('active');
        }
        
        podItem.innerHTML = `
            <div><strong>ID:</strong> ${truncateText(pod.id, 12)}</div>
            <div><strong>Signer:</strong> ${pod.signer}</div>
        `;
        
        podItem.addEventListener('click', () => {
            selectedPodId = pod.id;
            
            // Save selected POD to local storage
            saveSelectedPod();
            
            loadPodDetails(pod.id);
            
            // Update active class
            document.querySelectorAll('.pod-item').forEach(item => {
                item.classList.remove('active');
            });
            podItem.classList.add('active');
            
            // Switch to view tab
            tabButtons.forEach(btn => btn.classList.remove('active'));
            tabContents.forEach(content => content.classList.remove('active'));
            document.querySelector('[data-tab="view-pod"]').classList.add('active');
            document.getElementById('view-pod').classList.add('active');
        });
        
        podList.appendChild(podItem);
    });
}

// Load POD details from the API
async function loadPodDetails(podId) {
    try {
        // Check if we have the pod details cached
        if (podDetailsCache[podId]) {
            renderPodDetails(podDetailsCache[podId]);
            return;
        }
        
        const response = await fetch(`${API_PODS}/${podId}`);
        
        if (!response.ok) {
            throw new Error('Failed to load POD details');
        }
        
        const pod = await response.json();
        
        // Cache the pod details
        podDetailsCache[podId] = pod;
        savePodDetailsCache();
        
        renderPodDetails(pod);
    } catch (error) {
        console.error('Error loading pod details:', error);
        showStatusMessage('Failed to load POD details', 'error');
    }
}

// Render POD details in the main panel
function renderPodDetails(pod) {
    // Convert pod entries to array for easier rendering
    const entriesArray = Object.entries(pod.entries).map(([key, value]) => ({
        key,
        value: formatPodValue(value)
    }));
    
    podDetails.innerHTML = `
        <div class="pod-details-container">
            <div class="pod-info">
                <h2>POD Details</h2>
                <p><strong>ID:</strong> ${pod.id}</p>
                <p><strong>Class:</strong> ${pod.pod_class}</p>
                <p><strong>Signer:</strong> ${pod.signer}</p>
                <p><strong>Valid:</strong> ${pod.is_valid ? 'Yes ✓' : 'No ✗'}</p>
            </div>
            
            <h3>Entries</h3>
            <div class="pod-entries">
                ${entriesArray.map(entry => `
                    <div class="pod-entry">
                        <div class="entry-name">${entry.key}</div>
                        <div class="entry-value-container">${entry.value}</div>
                    </div>
                `).join('')}
            </div>
        </div>
    `;
}

// Format POD values for display - this function is now replaced by the more
// flexible formatPodValue function with includeHtml parameter
function formatPodValue(value, includeHtml = true) {
    if (value === null || value === undefined) {
        return includeHtml ? '<em>null</em>' : 'null';
    }
    
    if (typeof value === 'object') {
        if ('Int' in value) {
            return includeHtml 
                ? `<span class="value-int">${value.Int}</span>` 
                : `${value.Int}`;
        }
        if ('String' in value) {
            return includeHtml 
                ? `<span class="value-string">"${value.String}"</span>` 
                : `"${value.String}"`;
        }
        if ('Bool' in value) {
            return includeHtml 
                ? `<span class="value-bool">${value.Bool}</span>` 
                : `${value.Bool}`;
        }
        if ('Dictionary' in value) return includeHtml ? `<span class="value-dict">[Dictionary]</span>` : "[Dictionary]";
        if ('Set' in value) return includeHtml ? `<span class="value-set">[Set]</span>` : "[Set]";
        if ('Array' in value) return includeHtml ? `<span class="value-array">[Array]</span>` : "[Array]";
        
        // For raw values or other object types
        return includeHtml 
            ? `<pre>${JSON.stringify(value, null, 2)}</pre>` 
            : JSON.stringify(value);
    }
    
    return String(value);
}

// Add a new entry row to the create POD form
function addEntryRow() {
    const entryRow = document.createElement('div');
    entryRow.className = 'entry-row';
    entryRow.innerHTML = `
        <input type="text" class="entry-key" placeholder="Key" required>
        <input type="text" class="entry-value" placeholder="Value" required>
        <select class="entry-type">
            <option value="string">String</option>
            <option value="int">Integer</option>
            <option value="bool">Boolean</option>
        </select>
        <button type="button" class="remove-entry-btn">✕</button>
    `;
    
    entriesContainer.appendChild(entryRow);
}

// Handle form submission to create a new POD
async function handleCreatePod(e) {
    e.preventDefault();
    
    const signer = document.getElementById('signer').value.trim();
    const entryRows = entriesContainer.querySelectorAll('.entry-row');
    
    const entries = {};
    for (const row of entryRows) {
        const key = row.querySelector('.entry-key').value.trim();
        const value = row.querySelector('.entry-value').value.trim();
        const type = row.querySelector('.entry-type').value;
        
        if (!key || !value) {
            showStatusMessage('All entries must have both key and value', 'error');
            return;
        }
        
        // Convert the value based on its type
        let convertedValue;
        switch (type) {
            case 'int':
                if (!/^-?\d+$/.test(value)) {
                    showStatusMessage(`Value for key '${key}' is not a valid integer`, 'error');
                    return;
                }
                convertedValue = parseInt(value, 10);
                break;
            case 'bool':
                if (value.toLowerCase() !== 'true' && value.toLowerCase() !== 'false') {
                    showStatusMessage(`Value for key '${key}' is not a valid boolean (true/false)`, 'error');
                    return;
                }
                convertedValue = value.toLowerCase() === 'true';
                break;
            default: // string
                convertedValue = value;
        }
        
        entries[key] = convertedValue;
    }
    
    try {
        const response = await fetch(API_PODS, {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json'
            },
            body: JSON.stringify({
                signer,
                entries
            })
        });
        
        if (!response.ok) {
            const errorData = await response.json();
            throw new Error(errorData.error || 'Failed to create POD');
        }
        
        const data = await response.json();
        showStatusMessage(`POD created successfully with ID: ${data.id}`, 'success');
        
        // Reset form
        createPodForm.reset();
        entriesContainer.innerHTML = '';
        addEntryRow(); // Add one empty row
        
        // After creating a new pod, fetch the pod details
        const podResponse = await fetch(`${API_PODS}/${data.id}`);
        const podData = await podResponse.json();
        
        // Add the new pod to the list and save to localStorage
        const newPod = {
            id: podData.id,
            pod_class: podData.pod_class,
            signer: podData.signer,
            created_at: podData.created_at
        };
        
        console.log('Adding new pod to array:', newPod);
        
        // Make sure pods is an array
        if (!Array.isArray(pods)) {
            pods = [];
        }
        
        pods.push(newPod);
        console.log('Pods array after adding:', pods);
        savePods();
        
        // Cache the pod details
        podDetailsCache[podData.id] = podData;
        savePodDetailsCache();
        
        // Select the new pod
        selectedPodId = data.id;
        saveSelectedPod();
        
        // Render the updated list
        renderPodList();
        
        // Load and show the new pod details
        renderPodDetails(podData);
        
        // Switch to view tab
        tabButtons.forEach(btn => btn.classList.remove('active'));
        tabContents.forEach(content => content.classList.remove('active'));
        document.querySelector('[data-tab="view-pod"]').classList.add('active');
        document.getElementById('view-pod').classList.add('active');
        
    } catch (error) {
        console.error('Error creating pod:', error);
        showStatusMessage(error.message, 'error');
    }
}

// Helper to show status messages
function showStatusMessage(message, type = 'success') {
    const existingMessage = document.querySelector('.status-message');
    if (existingMessage) {
        existingMessage.remove();
    }
    
    const messageElement = document.createElement('div');
    messageElement.className = `status-message ${type}`;
    messageElement.textContent = message;
    
    const currentTab = document.querySelector('.tab-content.active');
    currentTab.insertAdjacentElement('afterbegin', messageElement);
    
    // Auto-remove after 5 seconds
    setTimeout(() => {
        if (messageElement.parentNode) {
            messageElement.remove();
        }
    }, 5000);
}

// Helper to truncate text with ellipsis
function truncateText(text, maxLength) {
    if (text.length <= maxLength) return text;
    return text.substring(0, maxLength) + '...';
}

// Handle visualization of pods
async function handleVisualizePods() {
    try {
        // First check if we have pods in memory
        if (pods.length === 0) {
            // Try loading from storage first
            if (!loadPodsFromStorage()) {
                // If nothing in storage, try from server
                await loadPods();
            }
        }
        
        console.log('Visualization - current pods:', pods);
        
        if (pods.length === 0) {
            visualizationContainer.innerHTML = '<p>No PODs available to visualize</p>';
            return;
        }
        
        // Make sure pod details cache is loaded
        if (Object.keys(podDetailsCache).length === 0) {
            loadPodDetailsCacheFromStorage();
        }
        
        console.log('Visualization - pod details cache:', Object.keys(podDetailsCache));
        
        // Fetch full pod details for all pods, using cache when available
        const podDetails = await Promise.all(
            pods.map(async pod => {
                try {
                    console.log(`Getting details for pod ${pod.id}`);
                    
                    if (podDetailsCache[pod.id]) {
                        console.log(`Using cached details for pod ${pod.id}`);
                        return podDetailsCache[pod.id];
                    } else {
                        console.log(`Fetching details for pod ${pod.id} from server`);
                        try {
                            const response = await fetch(`${API_PODS}/${pod.id}`);
                            if (!response.ok) {
                                throw new Error(`Server returned ${response.status} ${response.statusText}`);
                            }
                            
                            const data = await response.json();
                            
                            // Cache the result
                            podDetailsCache[pod.id] = data;
                            savePodDetailsCache();
                            
                            return data;
                        } catch (fetchError) {
                            console.error(`Error fetching pod ${pod.id}:`, fetchError);
                            // Return a basic structure to avoid breaking the visualization
                            return {
                                id: pod.id,
                                pod_class: pod.pod_class || 'Unknown',
                                signer: pod.signer || 'Unknown',
                                entries: {},
                                is_valid: false
                            };
                        }
                    }
                } catch (podError) {
                    console.error(`Error handling pod ${pod.id}:`, podError);
                    // Return a placeholder for failed pods
                    return {
                        id: pod.id,
                        pod_class: 'Error',
                        signer: 'Error',
                        entries: { error: `Failed to load: ${podError.message}` },
                        is_valid: false
                    };
                }
            })
        );
        
        console.log('Visualization - got pod details:', podDetails);
        
        const type = visualizationType.value;
        
        // Clear the container
        visualizationContainer.innerHTML = '';
        
        switch (type) {
            case 'tree':
                renderTreeVisualization(podDetails);
                break;
            case 'network':
                renderNetworkVisualization(podDetails);
                break;
            case 'json':
                renderJsonVisualization(podDetails);
                break;
            default:
                visualizationContainer.innerHTML = '<p>Unknown visualization type</p>';
        }
    } catch (error) {
        console.error('Error visualizing pods:', error);
        showStatusMessage('Failed to visualize PODs', 'error');
    }
}

// Render a tree visualization using D3.js
function renderTreeVisualization(podDetails) {
    try {
        // Create a hierarchical structure for the tree
        const root = {
            name: "PODs",
            children: podDetails.map(pod => {
                try {
                    return {
                        name: truncateText(pod.id, 8),
                        signer: pod.signer || 'Unknown',
                        id: pod.id,
                        children: Object.entries(pod.entries || {}).map(([key, value]) => {
                            try {
                                return {
                                    name: key,
                                    value: formatPodValue(value, false),
                                    pod_id: pod.id
                                };
                            } catch (entryError) {
                                console.warn(`Error processing entry ${key}:`, entryError);
                                return {
                                    name: key,
                                    value: '[Error processing value]',
                                    pod_id: pod.id
                                };
                            }
                        })
                    };
                } catch (podError) {
                    console.warn(`Error processing pod ${pod.id}:`, podError);
                    return {
                        name: truncateText(pod.id, 8),
                        signer: 'Error',
                        id: pod.id,
                        children: [{ 
                            name: 'error', 
                            value: `Error processing: ${podError.message}`,
                            pod_id: pod.id
                        }]
                    };
                }
            })
        };
        
        // Set up the visualization dimensions
        const width = visualizationContainer.clientWidth;
        const height = visualizationContainer.clientHeight;
        const margin = { top: 20, right: 120, bottom: 20, left: 120 };
        
        // Create SVG element
        const svg = d3.select(visualizationContainer)
            .append("svg")
            .attr("width", width)
            .attr("height", height)
            .append("g")
            .attr("transform", `translate(${margin.left},${margin.top})`);
        
        // Create the tree layout
        const tree = d3.tree().size([height - margin.top - margin.bottom, width - margin.left - margin.right]);
        
        // Assign hierarchy to data
        const hierarchyRoot = d3.hierarchy(root);
        
        // Compute the tree layout
        const treeData = tree(hierarchyRoot);
        
        // Add links between nodes
        svg.selectAll(".link")
            .data(treeData.links())
            .enter()
            .append("path")
            .attr("class", "link")
            .attr("d", d3.linkHorizontal()
                .x(d => d.y)
                .y(d => d.x));
        
        // Add nodes
        const node = svg.selectAll(".node")
            .data(treeData.descendants())
            .enter()
            .append("g")
            .attr("class", d => "node" + (d.children ? " node--internal" : " node--leaf"))
            .attr("transform", d => `translate(${d.y},${d.x})`);
        
        // Add circles to nodes
        node.append("circle")
            .attr("r", 5)
            .style("fill", d => {
                if (d.depth === 0) return "#999"; // Root
                if (d.depth === 1) return "#3498db"; // POD
                return "#2ecc71"; // Entry
            });
        
        // Add labels to nodes
        node.append("text")
            .attr("dy", ".35em")
            .attr("x", d => d.children ? -10 : 10)
            .style("text-anchor", d => d.children ? "end" : "start")
            .text(d => d.data.name)
            .append("tspan")
            .attr("class", "node-label")
            .attr("x", d => d.children ? -10 : 10)
            .attr("dy", "1.2em")
            .text(d => {
                try {
                    if (d.depth === 1 && d.data.signer) {
                        return `Signer: ${d.data.signer}`;
                    }
                    if (d.depth === 2 && d.data.value) {
                        return `Value: ${d.data.value}`;
                    }
                    return "";
                } catch (error) {
                    console.warn('Error generating label:', error);
                    return "[Error]";
                }
            });
        
        // Add tooltip for more info on hover
        const tooltip = d3.select(visualizationContainer)
            .append("div")
            .attr("class", "tooltip")
            .style("opacity", 0);
        
        node.on("mouseover", function(event, d) {
            try {
                if (d.depth >= 1) { // Only show tooltip for PODs and entries
                    tooltip.transition()
                        .duration(200)
                        .style("opacity", .9);
                    
                    let tooltipContent = "";
                    if (d.depth === 1) {
                        tooltipContent = `
                            <strong>POD ID:</strong> ${d.data.id}<br>
                            <strong>Signer:</strong> ${d.data.signer}<br>
                            <strong>Entries:</strong> ${d.data.children ? d.data.children.length : 0}
                        `;
                    } else if (d.depth === 2) {
                        tooltipContent = `
                            <strong>Key:</strong> ${d.data.name}<br>
                            <strong>Value:</strong> ${d.data.value || '[No value]'}<br>
                            <strong>POD ID:</strong> ${d.data.pod_id || '[Unknown]'}
                        `;
                    }
                    
                    tooltip.html(tooltipContent)
                        .style("left", (event.pageX - visualizationContainer.getBoundingClientRect().left + 10) + "px")
                        .style("top", (event.pageY - visualizationContainer.getBoundingClientRect().top - 28) + "px");
                }
            } catch (error) {
                console.warn('Error showing tooltip:', error);
            }
        })
        .on("mouseout", function() {
            tooltip.transition()
                .duration(500)
                .style("opacity", 0);
        });
    } catch (error) {
        console.error('Error rendering tree visualization:', error);
        visualizationContainer.innerHTML = `<div class="error">Error rendering tree visualization: ${error.message}</div>`;
    }
}

// Render a network visualization using D3.js
function renderNetworkVisualization(podDetails) {
    try {
        // Create nodes and links for the network
        const nodes = [];
        const links = [];
        
        // Add POD nodes
        podDetails.forEach(pod => {
            try {
                nodes.push({
                    id: pod.id,
                    group: 1, // POD group
                    signer: pod.signer || 'Unknown',
                    type: "pod"
                });
                
                // Add entry nodes and links to POD
                Object.entries(pod.entries || {}).forEach(([key, value]) => {
                    try {
                        const entryId = `${pod.id}-${key}`;
                        nodes.push({
                            id: entryId,
                            group: 2, // Entry group
                            key: key,
                            value: formatPodValue(value, false),
                            type: "entry"
                        });
                        
                        links.push({
                            source: pod.id,
                            target: entryId,
                            value: 1
                        });
                    } catch (entryError) {
                        console.warn(`Error processing entry ${key}:`, entryError);
                    }
                });
            } catch (podError) {
                console.warn(`Error processing pod ${pod.id}:`, podError);
            }
        });
    
        // Set up the visualization dimensions
        const width = visualizationContainer.clientWidth;
        const height = visualizationContainer.clientHeight;
        
        // Create SVG element
        const svg = d3.select(visualizationContainer)
            .append("svg")
            .attr("width", width)
            .attr("height", height);
        
        if (nodes.length === 0) {
            visualizationContainer.innerHTML = '<p>No valid POD data to visualize</p>';
            return;
        }
        
        // Define the forces for the simulation
        const simulation = d3.forceSimulation(nodes)
            .force("link", d3.forceLink(links).id(d => d.id).distance(100))
            .force("charge", d3.forceManyBody().strength(-300))
            .force("center", d3.forceCenter(width / 2, height / 2))
            .force("x", d3.forceX(width / 2))
            .force("y", d3.forceY(height / 2));
        
        // Add links
        const link = svg.append("g")
            .selectAll("line")
            .data(links)
            .enter()
            .append("line")
            .attr("class", "link");
        
        // Add node groups
        const node = svg.append("g")
            .selectAll("g")
            .data(nodes)
            .enter()
            .append("g")
            .attr("class", "node")
            .call(d3.drag()
                .on("start", dragStarted)
                .on("drag", dragged)
                .on("end", dragEnded));
        
        // Add circles to nodes
        node.append("circle")
            .attr("r", d => d.type === "pod" ? 10 : 5)
            .style("fill", d => d.type === "pod" ? "#3498db" : "#2ecc71");
        
        // Add labels to nodes
        node.append("text")
            .attr("dy", ".35em")
            .attr("x", d => d.type === "pod" ? 12 : 8)
            .text(d => {
                try {
                    if (d.type === "pod") {
                        return truncateText(d.id, 8);
                    } else {
                        return d.key;
                    }
                } catch (error) {
                    console.warn('Error rendering node label:', error);
                    return '[Error]';
                }
            });
        
        // Add tooltip for more info on hover
        const tooltip = d3.select(visualizationContainer)
            .append("div")
            .attr("class", "tooltip")
            .style("opacity", 0);
        
        node.on("mouseover", function(event, d) {
            try {
                tooltip.transition()
                    .duration(200)
                    .style("opacity", .9);
                
                let tooltipContent = "";
                if (d.type === "pod") {
                    tooltipContent = `
                        <strong>POD ID:</strong> ${d.id}<br>
                        <strong>Signer:</strong> ${d.signer || 'Unknown'}
                    `;
                } else {
                    tooltipContent = `
                        <strong>Key:</strong> ${d.key || 'Unknown'}<br>
                        <strong>Value:</strong> ${d.value || 'Unknown'}
                    `;
                }
                
                tooltip.html(tooltipContent)
                    .style("left", (event.pageX - visualizationContainer.getBoundingClientRect().left + 10) + "px")
                    .style("top", (event.pageY - visualizationContainer.getBoundingClientRect().top - 28) + "px");
            } catch (error) {
                console.warn('Error showing tooltip:', error);
            }
        })
        .on("mouseout", function() {
            tooltip.transition()
                .duration(500)
                .style("opacity", 0);
        });
        
        // Update positions during simulation
        simulation.on("tick", () => {
            link
                .attr("x1", d => d.source.x)
                .attr("y1", d => d.source.y)
                .attr("x2", d => d.target.x)
                .attr("y2", d => d.target.y);
            
            node
                .attr("transform", d => `translate(${d.x},${d.y})`);
        });
        
        // Drag functions
        function dragStarted(event, d) {
            if (!event.active) simulation.alphaTarget(0.3).restart();
            d.fx = d.x;
            d.fy = d.y;
        }
        
        function dragged(event, d) {
            d.fx = event.x;
            d.fy = event.y;
        }
        
        function dragEnded(event, d) {
            if (!event.active) simulation.alphaTarget(0);
            d.fx = null;
            d.fy = null;
        }
    } catch (error) {
        console.error('Error rendering network visualization:', error);
        visualizationContainer.innerHTML = `<div class="error">Error rendering network visualization: ${error.message}</div>`;
    }
}

// Render a JSON tree visualization
function renderJsonVisualization(podDetails) {
    const jsonContainer = document.createElement('div');
    jsonContainer.className = 'json-container';
    
    // Format the JSON for display
    const formattedJson = formatJsonForDisplay(podDetails);
    jsonContainer.innerHTML = formattedJson;
    
    visualizationContainer.appendChild(jsonContainer);
}

// The formatPodValue function has been moved up earlier in the code

// Format JSON for display with syntax highlighting
function formatJsonForDisplay(json) {
    try {
        // Use replacer function to handle circular references
        const getCircularReplacer = () => {
            const seen = new WeakSet();
            return (key, value) => {
                if (typeof value === 'object' && value !== null) {
                    if (seen.has(value)) {
                        return '[Circular Reference]';
                    }
                    seen.add(value);
                }
                return value;
            };
        };
        
        // Try to stringify with circular reference handler
        const jsonString = JSON.stringify(json, getCircularReplacer(), 2);
        
        if (!jsonString) {
            return '<div class="error">Failed to format JSON data</div>';
        }
        
        // Basic syntax highlighting
        return jsonString
            .replace(/("(\\u[a-zA-Z0-9]{4}|\\[^u]|[^\\"])*"(\s*:)?|\b(true|false|null)\b|-?\d+(?:\.\d*)?(?:[eE][+\-]?\d+)?)/g, match => {
                let cls = 'json-value-number';
                if (/^"/.test(match)) {
                    if (/:$/.test(match)) {
                        cls = 'json-key';
                        match = match.replace(/:$/, '');
                    } else {
                        cls = 'json-value-string';
                    }
                } else if (/true|false/.test(match)) {
                    cls = 'json-value-boolean';
                } else if (/null/.test(match)) {
                    cls = 'json-value-null';
                }
                
                return `<span class="${cls}">${match}</span>`;
            })
            .replace(/[{}[\],]/g, match => {
                return `<span class="json-bracket">${match}</span>`;
            });
    } catch (error) {
        console.error('Error in formatJsonForDisplay:', error);
        return `<div class="error">Error formatting JSON: ${error.message}</div>`;
    }
}