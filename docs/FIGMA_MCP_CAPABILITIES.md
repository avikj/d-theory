Skip to main content
Subscribe to Figma’s editorial newsletter
Maker Stories
Working Well
Inside Figma
Insights
Topics




JUNE 4, 2025
Introducing our MCP server: Bringing Figma into your workflow


Jake AlbaughDeveloper Advocate, Figma
INSIDE FIGMA
PRODUCT UPDATES
DEV MODE


Today we’re announcing the beta release of the Figma MCP server, which brings Figma directly into the developer workflow to help LLMs achieve design-informed code generation.




Until recently, the only way to provide design context to AI tools was to feed an image of a design or an API response to a chatbot. This has changed with the recent advent of Model Context Protocol (MCP), a standard for how applications provide context to LLMs. We set out to apply this standard with Figma’s MCP server, which allows developers to bring context from Figma into agentic coding tools like Copilot in VS Code, Cursor, Windsurf, and Claude Code. Whether it’s creating new atomic components with the proper variables and stylings or building out multi-layer application flows, we believe this server will provide a more efficient and accurate design-to-code workflow.

As a beta, this is only the beginning. Over the coming months, we plan to release a slew of updates, including features like remote server capabilities and deeper codebase integrations. With your feedback, we’ll continue to iterate on and expand our offering. You can provide feedback directly to us through this form. There’s a lot more to come, but first, let’s take a step back to share how we got here.

Watch Jake's lightning talk on how to align code to design intent.
Context is everything

Today, LLMs can create workable code. But if you ask a tool to write code with no other context beyond its training data, its output—while usable—likely won’t match the patterns found in the rest of your codebase. This is because every team approaches their codebase differently—with a different structure, framework, vocabulary, and workflow—and makes decisions that evolve their codebase based on their specific needs. All these differences compound into a unique fingerprint that’s difficult for LLMs to infer.

Recognizing and understanding these patterns requires additional context, and this is where agentic coding tools come into play. They gather context—from reading existing code, examining repository history, accessing documentation, and understanding database schemas—and feed it to LLMs so they can generate code in your IDE that’s precise, informed, and in line with your existing systems. MCP servers like Figma’s MCP server add onto this by bringing outside context from other tools like Figma into that workflow, so your code doesn't just match the fingerprint of your codebase, but that of your design, too.

Design context is critical for going from design to code. When it comes to understanding design intent, we need to consider a range of information that could be valuable based on what we’re asking an LLM to do. Getting this information right is important because the process of translating design to code is more than detailed inspection.

How we translate design intent for LLMs

When a developer opens a Figma file, the first thing they probably do is zoom all the way out to get a sense for order and structure. Then, they might process a sequence of screens or inferred logic, thinking about how they could structure the feature across different files in code. They audit as they build, making sure the patterns are right, interpreting placeholder content as something real they need to retrieve from the backend. Throughout the process of implementing a design, they’re generating different types of code and working across different altitudes—from under-the-hood details to higher-level patterns. To ensure that design intent translates to code, LLMs also need this holistic picture.

The Figma MCP server paints this picture for LLMs in a few key ways, supplementing visual information with more nuanced details around design intent, while also drawing from existing patterns and systems. Different tasks might require different combinations of these points of context, and often, the context we exclude is just as important as what we provide. This is why MCP servers, like ours, surface tools that represent specific types of context for LLMs. Our server also allows you to configure settings to give you control over what those tools return. Here’s a look at when to consider dialing up and down these points of context—depending on your setup and what you want to prioritize.

Pattern metadata

Since you have limited space in an LLM’s context window, the more information you can provide, the better. By giving the LLM the context from your designs, the fewer tokens it uses.
If you’ve already invested in a design system and leverage patterns like components, variables, and styles that are aligned between design and code, the Figma MCP server is a multiplier—we want to make sure that the LLM can benefit from these patterns, too. Agentic search techniques can take quite a bit of time to locate the right patterns, especially in large codebases. They may also find valid patterns that stray from those referenced in a design. By providing references to specific variables, components, and styles, the Figma MCP server can make generated code more precise, efficient, and reduce LLM token usage.


In this video, Jake provides some examples for how to bulk add code syntax to a variable collection with the plugin API.
For example, let’s say you’ve created a lot of alignment between design and code. If you only provide a screenshot of a component instance, the AI tool will spend a lot of time searching the codebase—like icon and component libraries—to identify the right component to use. If it doesn’t find a match, it will likely create a new component based on the screenshot. By contrast, if Figma knows which components you’re using, it can share the exact path to the code file the agent needs with Code Connect.

Similarly, if you take a screenshot of a red rectangle and prompt your agentic tool to use tokens, there might be many different tokens with the same red value. Figma knows which specific token is used, and can provide the name of that variable to the LLM via MCP. Even better, if you have provided code syntax in Figma for that variable, the Figma MCP server can provide that exact code to the LLM.

Screenshot of a selected design in Figma with Copilot chat output on the right. The output includes a typescript import statement for a Navigation components as well as a list of code representations for variables that are used in the design.
An example of the Code Connect and variables code syntax metadata that the Figma MCP server provides for a selection.
Screenshots

Designers often use imagery to represent a piece of interactive content—like using a picture of a map in a design to represent a live embedded map experience. In these scenarios, metadata may not fully communicate that interactive functionality to an LLM. With a screenshot, the Figma MCP server can provide that design context.
Teams build all types of complicated and compelling designs, and it’s often helpful to zoom out and think about the high-level view of a design before diving into the details. For example, when you’re trying to get a sense for the overall context—sequence of screens, sections, mobile and desktop responsive context—a high-level screenshot can provide the LLM information about the relationship between sections and nodes, and capture the overall flow in a way that style details can’t.

The value of this kind of visual information is more about what it tells us about design intent than it is a spec for the LLM to replicate one to one. The right code is aligned to design intent, not just pixels. We like to think of screenshots as supplemental information for the code response; a screenshot combined with Figma’s code outputs performs better than either on their own.

A screenshot of a layout design next to a GitHub Copilot chat interface. The output is a high level description of the design breaking it down into 15 named components with descriptions of what they represent.
An example of how you can use the get image tool to analyze a design in Figma. In this case, we’re asking Copilot to tell us approximately how many components we’ll need to add to our design system.
Interactivity

Code examples can describe design behavior already defined in Figma, or already connected to the codebase. Pseudocode, which you can think of as a code prototype, is often a great way to give an LLM context that’s more effective than simply describing properties—especially if the pseudocode is also informed by the codebase, with features like code syntax for variables and Code Connect for components.

This sample code can be helpful in a few scenarios, like when you’re looking to describe a fully encapsulated piece of functionality. A psuedo-representation of a stateful component is useful to an LLM in a way that a tree of Figma metadata is not. It’s also useful to represent a sequence of UI—rather than inspecting them independently as metadata—to focus on the differences between them.

A screenshot of an image gallery next to the codebase. The codebase has a React and Tailwind code representation of the design.
An example of the React and Tailwind code the MCP server provides by default. In this case, it’s a working React representation of this image gallery. LLMs can make use of this interactive code representation as they incorporate this design into the codebase.
Content

We want to make sure that we’re getting what’s implied by a design out of Figma, too. Even placeholder content in Figma can be representative of design context and informative for LLMs. Content like text, svg, images, layer names, and annotations can help LLMs derive how to fill the interface with the data model on the code side.

A screenshot of a user review card ui selected in Figma with Copilot output next to it describing the UI accurately as well as some actions it can take next.
Here we can see that the text and layer names for the current Figma selection show up in the MCP server’s React output and allow the LLM to tell us quite a bit of information about the design.
Design-informed code generation

Many developers are already using AI to work more efficiently in their IDEs, and we’re excited to accelerate those workflows while keeping output consistent and at a high fidelity. Today, that starts with three tools in the MCP server that allow you to get context from Figma for the current selection or specific node id: one for code, another for images, and a third for variable definitions. You can change the type of response the code tool returns inside your server settings, which allows for fine tuning based on the task at hand. You can enable the more interactive code representation with React and Tailwind, with more options to come down the line. Code Connect ensures that generated code aligns with your codebase, allowing you to see component mappings and any code syntax you add for your variables will also be surfaced.


As we launch the Figma MCP server in beta, we’re looking for your feedback on current capabilities, which will inform what we build down the line. Based on early testing, we’re already working on a few improvements, starting with making the MCP experience available without needing the Figma desktop app, so it’s easier for teams to onboard and collaborate from anywhere. We’re also working on a deeper codebase integration and simpler Code Connect experience with a more intuitive setup. Future versions will explore features that support annotations, Grid, and more.

This is just the first step in our commitment to building a better design-to-code experience with faster handoff, smarter outputs, and more efficient workflows. You can access Figma’s MCP server with any Dev or Full seat, and look out for more updates as we continue to invest in this space. We can’t wait to hear what you think.

Subscribe to Figma’s editorial newsletter
Enter email*
I agree to opt-in to Figma's mailing list.*

By clicking “Subscribe” you agree to our TOS and Privacy Policy.

PRODUCT

Figma Design
Dev Mode
FigJam
Figma Slides
Figma DrawNEW
Figma BuzzBETA
Figma SitesBETA
Figma MakeNEW
AI
Downloads
Release notes
PLANS

Pricing
Enterprise
Organization
Professional
USE CASES

UI design
UX design
Wireframing
Diagramming
Prototyping
Brainstorming
Presentation Maker
Online whiteboard
Strategic planning
Mind mapping
Concept map
AI app builder
AI prototype generator
AI website builder
AI wireframe generator
RESOURCES

Blog
Best practices
QR code generator
Color wheel
Colors
Color picker
Color palettes
Color palette generator
Color contrast checker
Font library
Lorem ipsum generator
Templates
Developers
Integrations
Affiliate program
Resource library
Reports and insights
Support
Status
Legal and privacy
Modern slavery statement (UK)
Climate disclosure statement
COMPANY

Events
Customers
Careers
Newsroom
Investors
Do Not Sell/Share My Personal Info + Opt-Out
