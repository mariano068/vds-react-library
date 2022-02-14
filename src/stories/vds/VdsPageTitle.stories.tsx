import { storiesOf } from '@storybook/react';
import React from 'react';
import { muiTheme } from 'storybook-addon-material-ui5';
import { version } from '../../../package.json';
import CodeHighlight from '../shared/CodeHighlight';
import { Highlight } from '../shared/Highlight';
import { BaseStoryLayout } from '../shared/StoryLayouts';
import { PageTitle_Default_Example, pageTitle_default_example_snippet, PageTitle_WithDescription_Example, pageTitle_withDescription_example_snippet, PageTitle_WithoutBreadcrumb_Example, pageTitle_withoutBreadcrumb_example_snippet } from '../snippets/VdsPageTitle.snippets';

const storyTitle = 'Page title';

storiesOf(`vds@${version}`, module)
  .addDecorator(muiTheme())
  .add(storyTitle, () => (
    <BaseStoryLayout storyTitle={storyTitle}>
      <p>Page title defines a specific area, always placed on the top of the page and below the header, with specific information regarding the name of the page and all the navigation indication required (i.e. breadcrumb, page information, section title…).</p>
      <h3>Overview</h3>
      <p>Page title has 2 states: extended and reduced. By default, page titles are set to extended. The component is set to extended state until the user scrolls down and the title page component reaches the top margin of the window. The extended page title now changes into reduced state becoming a fixed element on top of the page. The space dedicated to page description or explaination text can also contain a breadcrumb to ease the navigation</p>
      <CodeHighlight>
        <PageTitle_Default_Example />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{pageTitle_default_example_snippet}</Highlight>
      <CodeHighlight>
        <PageTitle_WithDescription_Example />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{pageTitle_withDescription_example_snippet}</Highlight>
      <CodeHighlight>
        <PageTitle_WithoutBreadcrumb_Example />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{pageTitle_withoutBreadcrumb_example_snippet}</Highlight>
    </BaseStoryLayout>
  ));
