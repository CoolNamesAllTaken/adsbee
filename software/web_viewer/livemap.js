console.log("This is a JS file loaded by the browser");


function getColorForAltitude(value) {
    // Assume that planes can fly between 0 and 40000 feet
    const scale = d3.scaleLinear().domain([0, 40000]).range(['blue', 'red'])
    console.log("Color for altitude:", scale(value))
    console.log("Value:", value)
    return scale(value)
}


// CSBee lines have the following format:
// #A:ICAO,FLAGS,CALL,SQUAWK,ECAT,LAT,LON,ALT_BARO,ALT_GEO,
// TRACK,VELH,VELV,SIGS,SIGQ,ESFPS,SFPS,SYSINFO,CRC/r/n
function parseCsbeeLine(line) {
  const fields = line.split(",");
    if (fields.length < 8) {
        console.error("Received invalid CSBee line:", line);
        return [];
    }
    if (fields[0].split(":")[0] !== "#A") {
        if (fields[0].split(":")[0] === "#S") {
            console.log("Stats:", fields);
            return [];
        }
        console.error("Received invalid CSBee line:", line);
        return [];
    }
    const latitude = fields[5]
    const longitude = fields[6]
    const heading_degrees = fields[9]
    const altitude_feet = fields[7]
    const airspeed_knots = fields[10]
    const color = getColorForAltitude(altitude_feet);
    const esfps = parseInt(fields[14])
    const sfps = parseInt(fields[15])
    const planeWasUpdated = (esfps !== 0 || sfps !== 0);
    console.log("esfps:", fields[14]);
    console.log("sfps:", fields[15]);
    console.log("Plane was updated:", planeWasUpdated);
    return [fields[0].split(":")[1], latitude, longitude, heading_degrees, color,
            altitude_feet, airspeed_knots, planeWasUpdated];
}

class LineBreakTransformer {
    constructor() {
      this.container = '';
    }
  
    transform(chunk, controller) {
      this.container += chunk;
      const lines = this.container.split('\r\n');
      this.container = lines.pop();
      lines.forEach(line => controller.enqueue(line));
    }
  
    flush(controller) {
      if (this.container) {
        controller.enqueue(this.container);
      }
    }
  }
  
  async function readSerialContinuously(port) {
    const textDecoder = new TextDecoderStream();
    const readableStreamClosed = port.readable.pipeTo(textDecoder.writable);
    const reader = textDecoder.readable
      .pipeThrough(new TransformStream(new LineBreakTransformer()))
      .getReader();
  
    try {
      while (true) {
        const { value, done } = await reader.read();
        if (done) {
          // The stream has been canceled.
          break;
        }
        // Process the line here
        processLine(value);
      }
    } catch (error) {
      console.error('Error reading serial data:', error);
    } finally {
      reader.releaseLock();
      await readableStreamClosed.catch(() => { /* Ignore the error */ });
    }
  }
  
  function processLine(line) {
    const fields = parseCsbeeLine(line);
    if (fields.length === 8) {
        if (!mapHasBeenCreated) {
            console.log("Creating Leaflet map for planes");
            console.log(fields);
            createLeafletMapForPlanes("leaflet-map", ...fields);
            mapHasBeenCreated = true;
        } else {
            console.log("Updating Leaflet map for planes");
            console.log(fields);
            updateLeafletMapForPlanes("leaflet-map", ...fields);
        }
    }
    else {
        if (!mapHasBeenCreated) {
            const mapContainer = document.getElementById("leaflet-map");
            mapContainer.innerHTML = "No data received yet";
        }
    }
  }


async function connectToSerialPort() {
  if ("serial" in navigator) {
    console.log("Web Serial API is supported");
  } else {
    console.log("Web Serial API is not supported in this browser");
    return
  }
  try {
    const port = await navigator.serial.requestPort();
    await port.open({ baudRate: 9600 });
    readSerialContinuously(port);
  } catch (error) {
    console.error("Error:", error);
  }
}

var activeLeafletMaps = {}
L.Map.addInitHook(function () {
    activeLeafletMaps[this._container.id] = this
})

var planes = {}


function makeNewIcon(color, heading) {
    return L.divIcon({className: 'leaflet-icon',
        html: `<span class='material-symbols-outlined' style='color: ${color}; transition: all 1s; transform: rotate(${heading}deg)'>flight</span>`})
}


function makeNewMarker(lat, lon, color, heading) {
    const iconWithColor = makeNewIcon(color, heading)
    let marker = L.marker([lat, lon], {icon: iconWithColor})
    return marker
}

function createLeafletMapForPlanes(parentContainer, id, lat, lon, heading, color, altitude, airspeed, planeWasUpdated) {
    // Creates or updates a Leaflet map
    console.log("createLeafletMapForPlanes");
    console.log(parentContainer, id, lat, lon, heading, color);
    let map;
    let scale;
    if (parentContainer in activeLeafletMaps) {
        map = activeLeafletMaps[parentContainer]
        map.remove()
    }
    const parentElement = document.getElementById(parentContainer)
    parentElement.innerHTML = ''
    map = L.map(parentContainer)
    L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {
        attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors'
    }).addTo(map);
    let mapViewIsSet = false
    if (!mapViewIsSet && lat !== null && lon !== null) {
        map.setView([lat, lon], 10)
        mapViewIsSet = true
    }
    if ((lat !== null && lon !== null) && (parseInt(lat) !== 0 || parseInt(lon) !== 0)) {
        let marker = makeNewMarker(lat, lon, color, heading)
        marker.addTo(map)
            .bindPopup(
                buildPopupContent(id, altitude, airspeed, 0),
                {autoClose:false}
              )
        planes[id] = {"marker": marker, "secondsSinceNew": 0}
    }
}

function buildPopupContent(id, altitude, airspeed, secondsSinceNew) {
    return `ICAO address: <b>${id}</b><br>Altitude: ${altitude} ft<br>Airspeed: ${airspeed} knots<br>Time since last update: ${secondsSinceNew} seconds`
    // return `<b>${id}</b>:${altitude}ft:${airspeed}kts:${secondsSinceNew}s`
}

function updateLeafletMapForPlanes(parentContainer, id, lat, lon, heading, color, altitude, airspeed, planeWasUpdated) {
    // Updates a Leaflet map with new data
    let map;
    if (parentContainer in activeLeafletMaps) {
        map = activeLeafletMaps[parentContainer]
    }
    else {
        console.error('No map found')
        return
    }
    if (lat === null || lon === null) {
        console.error('No data')
        return
    }

    let markerData = planes[id]
    let marker = null
    if ((lat !== null && lon !== null) && (parseInt(lat) !== 0 || parseInt(lon) !== 0)) {
        if (markerData === undefined) {
            console.log('Creating new marker')
            marker = makeNewMarker(lat, lon, color, heading)
            planes[id] = {"marker": marker, "secondsSinceNew": 0}
            marker.addTo(map).bindPopup(buildPopupContent(id, altitude, airspeed, 0),
            {autoClose:false})
        }
        else {
            marker = markerData.marker
            if (planeWasUpdated) {
                console.log("Updating existing marker (updated)")
                const timeSinceLastUpdate = 0
                marker.setPopupContent(buildPopupContent(id, altitude, airspeed, timeSinceLastUpdate))
                marker.setIcon(makeNewIcon(color, heading))
                marker.setLatLng([lat, lon])
                planes[id].secondsSinceNew = 0
            }
        }
    }
}

setInterval(function() {
    const map = activeLeafletMaps["leaflet-map"]
    for (let p of Object.keys(planes)) {
        planes[p].secondsSinceNew += 1
        let previous = planes[p].marker.getPopup().getContent()
        console.log("Updating popup content (unattached)")
        planes[p].marker.setPopupContent(previous.replace(/Time since last update: \d+ seconds/, `Time since last update: ${planes[p].secondsSinceNew} seconds`))
        // Make the color of the plane icon fade to transparent gradually
        planes[p].marker.color 
        if (planes[p].secondsSinceNew > 61) {
            console.log("removing out-of-date marker")
            map.removeLayer(planes[p].marker)
            delete planes[p]
        }
    }
}, 1000)
var mapHasBeenCreated = false
const startConnectionButton = document.getElementById("start-connection");
startConnectionButton.addEventListener("click", connectToSerialPort);
