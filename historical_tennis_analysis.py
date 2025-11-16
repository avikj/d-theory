import pandas as pd
import plotly.express as px
import plotly.graph_objects as go

# Load historical tennis data (example: download from tennis-data.co.uk)
# For demo, create mock data
data = {
    'Player': ['Player A', 'Player B', 'Player C'],
    'Wins': [50, 45, 40],
    'Aces_Avg': [8, 6, 7],
    'Serve_Speed_Avg': [125, 122, 118]
}
df = pd.DataFrame(data)

# Create visualizations
fig1 = px.bar(df, x='Player', y='Wins', title='Historical Wins by Player')
fig2 = px.scatter(df, x='Serve_Speed_Avg', y='Aces_Avg', text='Player', title='Serve Speed vs Aces')

# Save to HTML for OBS
fig1.write_html('historical_wins.html')
fig2.write_html('serve_aces.html')

print("Historical analysis saved to HTML files. Open in OBS as browser sources.")